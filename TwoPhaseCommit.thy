theory TwoPhaseCommit
  imports Main
begin

datatype co_state = CoInit | CoWait | CoCommit | CoAbort
datatype pa_state = PaInit | PaReady | PaCommit | PaAbort

type_synonym system_state = "co_state * (nat \<Rightarrow> pa_state)"

definition init :: "nat \<Rightarrow> system_state" where
  "init N = (CoInit, \<lambda>i. if i < N then PaInit else undefined)"

fun co_abort :: "system_state \<Rightarrow> system_state" where
  "co_abort (CoInit, p) = (CoAbort, p)"
| "co_abort (c, p) = (c, p)"

fun co_commit :: "system_state \<Rightarrow> system_state" where
  "co_commit (CoInit, p) = (CoWait, p)"
| "co_commit (c, p) = (c, p)"

(* CoTimeout can be simulated by co_abort*)

fun co_act :: "nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "co_act N (CoWait, ps) = (
    if (\<forall>i < N. ps i = PaReady) then
      (CoCommit, ps)
    else if (\<exists>i < N. ps i = PaAbort) then
      (CoAbort, ps)
    else
      (CoWait, ps)
  )"
| "co_act N (c, p) = (c, p)"

fun pa_abort :: "nat \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "pa_abort N i (c, ps) = 
  (
    if i \<ge> N then 
      (c, ps)
    else if (ps i = PaInit) then
      (c, ps(i := PaAbort))
    else
      (c, ps)
  )"


fun pa_act :: "nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "pa_act N (CoWait, ps) = (CoWait, \<lambda>i. if i < N \<and> ps i = PaInit then PaReady else ps i)"
| "pa_act N (CoCommit, ps) = (CoCommit, \<lambda>i. if i < N \<and> ps i = PaReady then PaCommit else ps i)"
| "pa_act N (CoAbort, ps) = (CoAbort, \<lambda>i. if i < N \<and> ps i = PaInit then PaAbort else ps i)"
| "pa_act N (c, ps) = (c, ps)"

inductive valid_sys :: "system_state \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_sys (init N) N"
| "\<lbrakk>valid_sys s N ;
   s' = co_abort s\<rbrakk> \<Longrightarrow> 
   valid_sys s' N"
| "\<lbrakk>valid_sys s N;
   s' = co_commit s \<rbrakk> \<Longrightarrow> 
   valid_sys s' N"
| "\<lbrakk>valid_sys s N;
    s' = co_act N s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"
| "\<lbrakk>valid_sys s N;
    s' = pa_act N s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"
| "\<lbrakk>valid_sys s N;
    x < N;
    s' = pa_abort N x s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"

(*
lemma first_phase_no_commit:
  assumes "valid_sys s N"
    and "(fst s = CoInit) \<or> (fst s = CoWait)"
  shows "\<not>(\<exists>x < N. ((snd s) x) = PaCommit)"
  sorry
*)

lemma co_commit_pa_no_abort:
  assumes "valid_sys s N"
    and "fst s = CoCommit"
  shows "\<not>(\<exists>x < N. ((snd s) x) = PaAbort)"
  sorry

lemma co_abort_pa_no_commit:
  assumes "valid_sys s N"
    and "fst s = CoAbort"
  shows "\<not>(\<exists>x < N. ((snd s) x) = PaCommit)"
  sorry

lemma pa_init_pa_no_commit:
  assumes "valid_sys s N"
    and "\<exists>x < N. ((snd s) x) = PaInit"
  shows "\<not>(\<exists>y < N. ((snd s) y) = PaCommit)"
  sorry

fun consistent_pa_states :: "pa_state \<Rightarrow> pa_state \<Rightarrow> bool" where
  "consistent_pa_states PaCommit PaAbort = False"
| "consistent_pa_states PaAbort PaCommit = False"
| "consistent_pa_states _ _ = True"

lemma safety:
  assumes "valid_sys s N"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states ((snd s) x) ((snd s) y)"
using assms proof (induction s N arbitrary: x y rule: valid_sys.induct)
  case (1 Init N)
  then show ?case 
    by (simp add: init_def)
next
  case (2 s N s')
  then show ?case
    by (metis co_abort.elims eq_snd_iff)
next
  case (3 s N s')
  then show ?case
    by (metis co_commit.elims snd_conv)
next
  case (4 s N s')
  then show ?case 
    by (smt (verit, del_insts) co_act.simps(1) co_act.simps(2) co_act.simps(3) co_act.simps(4) co_state.exhaust prod.collapse prod.inject)
next
  case (5 s N s')
  obtain c ps where cps_def: "(c, ps) = s"
    using prod.collapse by blast
  then show ?case 
  proof (cases "c")
    case CoInit
    then show ?thesis
      using "5.IH" "5.hyps"(2) "5.prems"(1) "5.prems"(2) cps_def by force
  next
    case CoWait
    then show ?thesis
      using "5.IH" "5.hyps"(2) "5.prems"(1) "5.prems"(2) cps_def by auto
  next
    case CoCommit
    then show ?thesis
      using "5.hyps"(1) "5.hyps"(2) "5.prems"(1) "5.prems"(2) 
        co_commit_pa_no_abort 
        consistent_pa_states.elims(3) cps_def by fastforce
  next
    case CoAbort
    then show ?thesis
      using "5.hyps"(1) "5.hyps"(2) "5.prems"(1) "5.prems"(2) 
        co_abort_pa_no_commit 
        consistent_pa_states.elims(3) cps_def by fastforce
  qed
next
  case (6 s N x s')
  then show ?case 
  proof (cases "x \<ge> N")
    case True
    then show ?thesis
      using "6.prems"(1) by auto
  next
    case False
    obtain c ps where cps_def: "(c, ps) = s"
    using prod.collapse by blast 
    then show ?thesis 
    proof (cases "ps x = PaInit")
      case True
      then show ?thesis
        by (metis (full_types) "6.hyps"(1) "6.hyps"(2) "6.hyps"(3) "6.prems"(2) 
            consistent_pa_states.elims(3) cps_def fun_upd_apply pa_abort.simps pa_init_pa_no_commit 
            pa_state.distinct(3) pa_state.distinct(5) pa_state.simps(12) snd_conv)
    next
      case False
      then show ?thesis
        by (smt (verit, del_insts) "6.IH" "6.hyps"(1) "6.hyps"(3) "6.prems"(1) "6.prems"(2) 
            consistent_pa_states.elims(3) cps_def fun_upd_other fun_upd_same pa_abort.simps 
            pa_init_pa_no_commit snd_conv)
    qed
  qed
qed



end
