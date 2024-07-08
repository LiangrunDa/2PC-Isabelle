theory TwoPhaseCommit
  imports Main
begin

datatype co_state = CoInit | CoWait | CoCommit | CoAbort
datatype pa_state = PaInit | PaReady | PaCommit | PaAbort

type_synonym system_state = "co_state * (nat \<Rightarrow> pa_state)"

fun consistent_pa_states :: "pa_state \<Rightarrow> pa_state \<Rightarrow> bool" where
  "consistent_pa_states PaCommit PaAbort = False"
| "consistent_pa_states PaAbort PaCommit = False"
| "consistent_pa_states _ _ = True"

definition init :: "nat \<Rightarrow> system_state" where
  "init N = (CoInit, \<lambda>i. if i < N then PaInit else undefined)"

fun co_abort :: "system_state \<Rightarrow> system_state" where
  "co_abort (CoInit, p) = (CoAbort, p)"
| "co_abort (c, p) = (c, p)"

fun co_commit :: "system_state \<Rightarrow> system_state" where
  "co_commit (CoInit, p) = (CoWait, p)"
| "co_commit (c, p) = (c, p)"

fun co_timeout :: "system_state \<Rightarrow> system_state" where
  "co_timeout (CoWait, p) = (CoAbort, p)"
| "co_timeout (c, p) = (c, p)"

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

fun pa_act :: "nat \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "pa_act N i (CoWait, ps) = (CoWait, if ps i = PaInit then ps (i := PaReady) else ps)"
| "pa_act N i (CoCommit, ps) = (CoCommit, if ps i = PaReady then ps (i := PaCommit) else ps)"
| "pa_act N i (CoAbort, ps) = (CoAbort, if ps i = PaInit then ps (i := PaAbort) else ps)"
| "pa_act N i (c, ps) = (c, ps)"

inductive valid_sys :: "system_state \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_sys (init N) N"  (*1*)
| "\<lbrakk>valid_sys s N ;
   s' = co_abort s\<rbrakk> \<Longrightarrow> 
   valid_sys s' N"        (*2*)
| "\<lbrakk>valid_sys s N;
   s' = co_commit s \<rbrakk> \<Longrightarrow> 
   valid_sys s' N"        (*3*)
| "\<lbrakk>valid_sys s N;
    s' = co_act N s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"       (*4*)
| "\<lbrakk>valid_sys s N;
    i < N;
    s' = pa_act N i s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"       (*5*)
| "\<lbrakk>valid_sys s N;
    i < N;
    s' = pa_abort N i s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"       (*6*)
| "\<lbrakk>valid_sys s N;
    s' = co_timeout s\<rbrakk> \<Longrightarrow>
    valid_sys s' N"       (*7*)


lemma co_act_ps_unchanged:
  assumes "co_act N (c, p) = (c', p')"
  shows "p = p'"
  by (smt (verit, best) assms co_act.simps(1) co_act.simps(2) co_act.simps(3) co_act.simps(4) co_state.exhaust prod.inject)


lemma co_init_pa_init_or_abort:
  assumes "valid_sys s N"
    and "fst s = CoInit"
    and "x < N"
  shows "((snd s) x = PaInit) \<or> ((snd s) x = PaAbort)"
using assms proof (induction s N arbitrary: x rule: valid_sys.induct)
  case (1 N)
  then show ?case
    using init_def by force
next
  case (2 s N s')
  then show ?case
    by (metis co_abort.elims co_state.distinct(5) split_pairs)
next
  case (3 s N s')
  then show ?case
    by (metis co_commit.elims co_commit.simps(4) co_state.distinct(1) split_pairs)
next
  case (4 s N s')
  then show ?case 
    by (smt (verit, ccfv_threshold) co_act.elims co_state.distinct(5) co_state.simps(4) fst_conv)
next
  case (5 s N s')
  then show ?case 
    by (smt (verit) co_state.exhaust eq_fst_iff pa_act.simps(1) 
        pa_act.simps(2) pa_act.simps(3) pa_act.simps(4))
next
  case (6 s N x s')
  then show ?case
    by (metis (no_types, lifting) fun_upd_other fun_upd_same pa_abort.simps split_pairs)
next
  case (7 s N s')
  then show ?case
    by (smt (verit) co_state.distinct(5) co_state.exhaust co_timeout.simps(1) co_timeout.simps(2) co_timeout.simps(3) co_timeout.simps(4) split_pairs)
qed

lemma co_wait_pa_init_or_abort_or_ready:
  assumes "valid_sys s N"
    and "fst s = CoWait"
    and "x < N"
  shows "((snd s) x = PaInit) \<or> ((snd s) x = PaAbort) \<or> ((snd s) x = PaReady)"
using assms proof (induction s N arbitrary: x rule: valid_sys.induct)
  case (1 N)
  then show ?case
    by (simp add: init_def)
next
  case (2 s N s')
  then show ?case 
    by (smt (verit, best) co_abort.simps(1) co_abort.simps(2) co_abort.simps(3) co_abort.simps(4) 
        co_init_pa_init_or_abort co_state.exhaust split_pairs)
next
  case (3 s N s')
  then show ?case 
    by (smt (verit, ccfv_threshold) co_commit.simps(1) co_commit.simps(2) co_commit.simps(3) 
        co_commit.simps(4) co_init_pa_init_or_abort co_state.exhaust split_pairs)
next
  case (4 s N s')
  then show ?case 
    by (smt (verit, ccfv_SIG) co_act.simps(2) co_act.simps(3) co_act.simps(4) co_act_ps_unchanged co_state.exhaust prod.collapse)
next
  case (5 s N s')
  then show ?case
    by (smt (verit, ccfv_SIG) co_state.exhaust fstI fun_upd_apply pa_act.simps(1) pa_act.simps(2) pa_act.simps(3) pa_act.simps(4) prod.exhaust_sel sndI)
next
  case (6 s N x s')
  then show ?case 
    by (smt (verit, ccfv_SIG) fun_upd_other fun_upd_same pa_abort.simps split_pairs)
next
  case (7 s N s')
  then show ?case
    by (smt (verit, ccfv_threshold) co_state.exhaust co_timeout.simps(1) co_timeout.simps(2) co_timeout.simps(3) co_timeout.simps(4) fst_swap old.prod.inject prod.swap_def prod_eqI snd_swap)
qed



lemma co_commit_pa_commit_or_ready:
  assumes "valid_sys s N"
    and "fst s = CoCommit"
    and "x < N"
  shows "(((snd s) x) = PaCommit) \<or> (((snd s) x) = PaReady)"
using assms proof (induction s N arbitrary: x rule: valid_sys.induct)
  case (1 N)
  then show ?case
    by (simp add: init_def)
next
  case (2 s N s')
  then show ?case
    by (metis (full_types) co_abort.elims co_state.distinct(11) co_state.simps(8) fst_conv)
next
  case (3 s N s')
  then show ?case 
    by (metis co_commit.cases co_commit.simps(1) co_commit.simps(2) co_commit.simps(3) 
        co_commit.simps(4) co_state.distinct(7) split_pairs)
next
  case (4 s N s')
  have "snd s' = snd s"
    using co_act_ps_unchanged
    by (metis "4.hyps"(2) prod.collapse)
  have "fst s' = CoCommit"
    by (simp add: "4.prems"(1))
  then show ?case 
    by (smt (verit, best) "4.IH" "4.hyps"(2) "4.prems"(2) \<open>snd s' = snd s\<close> co_act.simps(1) co_act.simps(2) co_act.simps(4) co_state.distinct(11) co_state.exhaust split_pairs)
next
  case (5 s N s')
  then show ?case 
    by (smt (verit, ccfv_SIG) co_state.exhaust fun_upd_other fun_upd_same pa_act.simps(1) pa_act.simps(2) pa_act.simps(3) pa_act.simps(4) prod.exhaust_sel prod.inject)
next
  case (6 s N x s')
  then show ?case 
    by (metis pa_abort.simps pa_state.distinct(1) pa_state.distinct(3) split_pairs)
next
  case (7 s N s')
  then show ?case
    by (metis Pair_inject co_state.simps(12) co_timeout.elims prod.exhaust_sel)
qed

corollary co_commit_pa_no_abort:
  assumes "valid_sys s N"
    and "fst s = CoCommit"
    and "x < N"
  shows "((snd s) x) \<noteq> PaAbort"
  using assms(1) assms(2) assms(3) co_commit_pa_commit_or_ready by fastforce


lemma co_abort_pa_init_or_ready_abort:
  assumes "valid_sys s N"
    and "fst s = CoAbort"
    and "x < N"
  shows "(((snd s) x) = PaInit) \<or> (((snd s) x) = PaReady) \<or>
        (((snd s) x) = PaAbort)"
  using assms proof (induction s N arbitrary: x rule: valid_sys.induct)
  case (1 N)
  then show ?case
    by (simp add: init_def)
next
  case (2 s N s')
(* apply case distinction, if fst s is CoAbort or CoWait *)
  then show ?case
    by (smt (verit, del_insts) co_abort.simps(1) co_abort.simps(2) co_abort.simps(3) 
        co_abort.simps(4) co_init_pa_init_or_abort co_state.exhaust split_pairs)
next
  case (3 s N s')
  then show ?case 
    by (smt (verit, best) co_commit.simps(1) co_commit.simps(2) co_commit.simps(3) 
        co_commit.simps(4) co_state.distinct(9) co_state.exhaust split_pairs)
next
  case (4 s N s')
  then show ?case 
    by (smt (verit, ccfv_SIG) co_act.simps(2) co_act.simps(3) co_act_ps_unchanged co_state.exhaust co_wait_pa_init_or_abort_or_ready prod.collapse)
next
  case (5 s N s')
  then show ?case 
    by (smt (verit, ccfv_threshold) co_state.exhaust fun_upd_other fun_upd_same pa_act.simps(1) pa_act.simps(2) pa_act.simps(3) pa_act.simps(4) prod.collapse snd_swap split_pairs)
next
  case (6 s N x s')
  then show ?case 
    by (smt (verit, ccfv_threshold) fun_upd_other fun_upd_same 
        pa_abort.simps pa_state.exhaust pa_state.simps(12) split_pairs)
next
  case (7 s N s')
  then show ?case 
    by (smt (verit) co_state.exhaust co_timeout.simps(1) co_timeout.simps(2) co_timeout.simps(3) co_timeout.simps(4) co_wait_pa_init_or_abort_or_ready fst_swap old.prod.inject prod.swap_def prod_eqI snd_swap)
qed
  

corollary co_abort_pa_no_commit:
  assumes "valid_sys s N"
    and "fst s = CoAbort"
    and "x < N"
  shows "((snd s) x) \<noteq> PaCommit"
  using assms(1) assms(2) assms(3) co_abort_pa_init_or_ready_abort by fastforce

lemma pa_init_pa_no_commit:
  assumes "valid_sys s N"
    and "\<exists>x < N. ((snd s) x) = PaInit"
    and "y < N"
  shows "((snd s) y) \<noteq> PaCommit"
  using assms proof (induction s N arbitrary: y rule: valid_sys.induct)
  case (1 N)
  then show ?case
    by (simp add: init_def)
next
  case (2 s N s')
  then show ?case
    by (smt (verit, best) co_abort.simps(1) co_abort.simps(2) co_abort.simps(3) co_abort.simps(4) co_state.exhaust split_pairs)
next
  case (3 s N s')
  then show ?case 
    by (metis (no_types, lifting) co_abort_pa_no_commit co_commit_pa_commit_or_ready co_init_pa_init_or_abort co_state.exhaust co_wait_pa_init_or_abort_or_ready pa_state.distinct(4) pa_state.distinct(8) pa_state.simps(12) pa_state.simps(2) valid_sys.intros(3))
next
  case (4 s N s')
  then show ?case 
    by (metis co_act_ps_unchanged eq_snd_iff)
next
  case (5 s N s')
  then show ?case 
    by (metis (no_types, lifting) co_abort_pa_no_commit co_commit_pa_commit_or_ready co_init_pa_init_or_abort co_state.exhaust co_wait_pa_init_or_abort_or_ready pa_state.distinct(1) pa_state.distinct(3) pa_state.distinct(7) pa_state.simps(12) valid_sys.intros(5))
next
  case (6 s N x s')
  then show ?case 
    by (metis (no_types, lifting) co_abort_pa_init_or_ready_abort co_commit_pa_commit_or_ready co_init_pa_init_or_abort co_state.exhaust co_wait_pa_init_or_abort_or_ready pa_state.distinct(1) pa_state.distinct(3) pa_state.distinct(7) pa_state.simps(12) valid_sys.intros(6))
next
  case (7 s N s')
  then show ?case
    by (smt (verit, ccfv_threshold) co_state.exhaust co_timeout.simps(1) co_timeout.simps(2) co_timeout.simps(3) co_timeout.simps(4) split_pairs)
qed

theorem safety:
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
      using "5.IH" "5.hyps"(3) "5.prems"(1) "5.prems"(2) cps_def by force
  next
    case CoWait
    then show ?thesis
      by (metis "5.hyps"(1) "5.hyps"(2) "5.hyps"(3) "5.prems"(1) "5.prems"(2) co_wait_pa_init_or_abort_or_ready consistent_pa_states.elims(3) cps_def fst_conv pa_act.simps(1) pa_state.distinct(3) pa_state.distinct(7) pa_state.simps(12) valid_sys.intros(5))
  next
    case CoCommit
    then show ?thesis
      using "5.hyps"(1) "5.hyps"(2) "5.prems"(1) "5.prems"(2) 
        co_commit_pa_no_abort 
        consistent_pa_states.elims(3) cps_def 
      by (metis "5.hyps"(3) fst_conv pa_act.simps(2) valid_sys.intros(5))
  next
    case CoAbort
    then show ?thesis
      using "5.hyps"(1) "5.hyps"(2) "5.prems"(1) "5.prems"(2) 
        co_abort_pa_no_commit 
        consistent_pa_states.elims(3) cps_def
      by (metis "5.hyps"(3) fst_conv pa_act.simps(3) valid_sys.intros(5))
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
next
  case (7 s N s')
  then show ?case 
    by (smt (verit) co_state.exhaust co_timeout.simps(1) co_timeout.simps(2) co_timeout.simps(3) co_timeout.simps(4) split_pairs)
qed



end
