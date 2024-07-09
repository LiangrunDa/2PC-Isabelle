theory TwoPhaseCommit
  imports Main
begin

text \<open>Two-Phase Commit (2PC) is a fundamental protocol used in distributed systems
to ensure that a series of operations across multiple nodes (or databases) either all succeed 
or all fail, maintaining the consistency of the system.

In this theory, we formalize the Two-Phase Commit protocol under the setting that a system 
consists of one coordinator and N participants, where N is arbitray but fixed.  The system 
is modeled as a state machine, where the state of the system is represented by a tuple of 
the coordinator's state and a function that maps each participant to its state. 
 
In reality, the coordinator and participants execute concurrently, possibly at different speeds
(in particular, a node may fail by stopping execution entirely). To model this, we say that the
system as a whole makes progress by one of the nodes performing an execution step, and nodes 
may perform steps in any order. The progress of the system is captured by a sequence of
execution steps, where each step is a transition from one state to another state.
\<close>

section \<open>Two-Phase Commit: Definitions\<close>

text \<open>Phase 2: Commit\<close>

datatype co_state = CoInit | CoWait | CoCommit | CoAbort
datatype pa_state = PaInit | PaReady | PaCommit | PaAbort

type_synonym system_state = "co_state * (nat \<Rightarrow> pa_state)"

fun consistent_pa_states :: "pa_state \<Rightarrow> pa_state \<Rightarrow> bool" where
  "consistent_pa_states PaCommit PaAbort = False"
| "consistent_pa_states PaAbort PaCommit = False"
| "consistent_pa_states _ _ = True"

text \<open>Phase 1: Prepare

If the client decides to commit a transaction, it sends a prepare message to the coordinator.
In our system, it is formalized as the co_commit step function. The coordinator then sends a
prepare message to each participant participating in the transaction, and each participant replies 
with a message indicating whether it is able to commit the transaction. It is formalized as 
the pa_act step function. If any participant fails to commit the transaction, it will turn to the
abort state, which is formalized as the pa_abort step function. 

If all participants are ready to commit, the coordinator decides to commit the transaction. If any
participant is to abort the transaction, the coordinator decides to abort the transaction. This is
formalized as the co_act step function. If the coordinator doesn't receive responses from all
participants within a certain time limit, it will abort the transaction. This is formalized as the
co_timeout step function.

If the client decides to abort the transaction, it sends an abort message to the coordinator.
It is formalized as the co_abort step function. All the participants will abort the transaction
after receiving the abort message from the coordinator, which is formalized as the pa_act step. 

Phase 2: Commit

If the coordinator decides to commit the transaction, it sends a commit message to each participant.
Each participant must commit the transaction after receiving the commit message from the coordinator.
If a participant fails to commit the transaction due to node crash, the coordinator must wait for the
participant to recover and there is no timeout for the recovery.

If the coordinator decides to abort the transaction, it sends an abort message to each participant.
Each participant must abort the transaction after receiving the abort message from the coordinator.

\<close>

text \<open>Initialize one coordinator and N participants.\<close>

definition init :: "nat \<Rightarrow> system_state" where
  "init N = (CoInit, \<lambda>i. if i < N then PaInit else undefined)"

text \<open>The client might abort a transaction\<close>

fun co_abort :: "system_state \<Rightarrow> system_state" where
  "co_abort (CoInit, p) = (CoAbort, p)"
| "co_abort (c, p) = (c, p)"

text \<open>The client might request a transaction commit\<close>

fun co_commit :: "system_state \<Rightarrow> system_state" where
  "co_commit (CoInit, p) = (CoWait, p)"
| "co_commit (c, p) = (c, p)"

text \<open>The coordinator should abort the transaction if it doesn't receive 
responses from all participants within a certain time limit.\<close>

fun co_timeout :: "system_state \<Rightarrow> system_state" where
  "co_timeout (CoWait, p) = (CoAbort, p)"
| "co_timeout (c, p) = (c, p)"

text \<open>The coordinator should commit the transaction if all participants are ready to commit.
Otherwise, it should abort the transaction if any participant is to abort the transaction.\<close>

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

text \<open>The participant might abort the transaction due to disk failure, constraint violation, etc.\<close>

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

text \<open>The participant can transition from the PaInit state to the PaReady state when the 
coordinator is waiting for responses from all participants. The participant can transition 
from the PaReady state to the PaCommit state if the coordinator decides to commit the 
transaction. The participant can transition from the PaInit state to the PaAbort state if the 
coordinator decides to abort the transaction.\<close>

fun pa_act :: "nat \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "pa_act N i (CoWait, ps) = (CoWait, if ps i = PaInit then ps (i := PaReady) else ps)"
| "pa_act N i (CoCommit, ps) = (CoCommit, if ps i = PaReady then ps (i := PaCommit) else ps)"
| "pa_act N i (CoAbort, ps) = (CoAbort, if ps i = PaInit then ps (i := PaAbort) else ps)"
| "pa_act N i (c, ps) = (c, ps)"

text \<open> A valid system is a sequence of execution steps. At each step, we compute the next state 
of the system using step functions defined above.\<close>

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

text \<open> The number of commit + abort nodes will monotonically increase. \<close>

fun aborts_commits :: "system_state \<Rightarrow> nat set" where
  "aborts_commits (c, ps) = {x. (ps x = PaAbort \<or> ps x = PaCommit)}"

fun progress :: "system_state \<Rightarrow> nat" where
  "progress (c, ps) = card (aborts_commits (c, ps))"

text \<open>Correctness of the Two-Phase Commit protocol is defined as: either all participants commit the
transaction or all participants abort the transaction. 

Safety property: If one commits, no one aborts. If one aborts, no one commits.
This is formalized as the safety theorem. 

Liveness property: Eventually all participants will reach to the commit state or abort state.
This is formalized as the liveness theorem. The number of commit + abort nodes is monotonically
increasing.\<close>

section \<open>invariant of step functions\<close>

subsection \<open>co_abort\<close>

lemma co_abort_CoWait:
  assumes "co_abort (c, p) = (c', p')"
    and "c' = CoWait"
  shows "c = CoWait"
  using assms apply (cases "((c, p))" rule: co_abort.cases)
  by auto

lemma co_abort_p_unchanged:
  assumes "co_abort (c, p) = (c', p')"
  shows "p = p'"
  using assms apply (cases "((c, p))" rule: co_abort.cases)
  by auto

lemma co_abort_CoCommit:
  assumes "co_abort (c, p) = (c', p')"
    and "c' = CoCommit"
  shows "c = CoCommit"
  using assms apply (cases "((c, p))" rule: co_abort.cases)
  by auto

lemma co_abort_CoAbort:
  assumes "co_abort (c, p) = (c', p')"
    and "c' = CoAbort"
  shows "c = CoInit \<or> c = CoAbort"
  using assms apply (cases "((c, p))" rule: co_abort.cases)
  by auto

subsection \<open>co_commit\<close>

lemma co_commit_CoWait:
  assumes "co_commit (c, p) = (c', p')"
    and "c' = CoWait"
  shows "c = CoWait \<or> c = CoInit"
  using assms apply (cases "((c, p))" rule: co_commit.cases)
  by auto

lemma co_commit_p_unchanged:
  assumes "co_commit(c, p) = (c', p')"
  shows "p = p'"
  using assms apply (cases "((c,p))" rule: co_commit.cases)
  by auto

lemma co_commit_CoCommit:
  assumes "co_commit (c, p) = (c', p')"
    and "c' = CoCommit"
  shows "c = CoCommit"
  using assms apply (cases "((c, p))" rule: co_commit.cases)
  by auto

lemma co_commit_CoAbort:
  assumes "co_commit (c, p) = (c', p')"
    and "c' = CoAbort"
  shows "c = CoAbort"
  using assms apply (cases "((c, p))" rule: co_commit.cases)
  by auto

subsection \<open>co_act\<close>

lemma co_act_p_unchanged:
  assumes "co_act N (c, p) = (c', p')"
  shows "p = p'"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

lemma co_act_CoInit:
  assumes "co_act N (c, p) = (c', p')"
    and "c' = CoInit"
  shows "c = CoInit"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

lemma co_act_CoWait:
  assumes "co_act N (c, p) = (c', p')"
    and "c' = CoWait"
  shows "c = CoWait"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

lemma co_act_CoCommit:
  assumes "co_act N (c, p) = (c', p')"
    and "c' = CoCommit"
  shows "c = CoWait \<or> c = CoCommit"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

lemma co_act_transition_no_init:
  assumes "co_act N (c, p) = (c', p')"
    and "c' = CoCommit"
    and "c = CoWait"
    and "x < N"
  shows "p' x = PaReady"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

lemma co_act_CoAbort:
  assumes "co_act N (c, p) = (c', p')"
    and "c' = CoAbort"
  shows "c = CoAbort \<or> c = CoWait"
  using assms apply (cases "(N, (c,p))" rule: co_act.cases)
  by (auto split: if_splits)

subsection \<open>pa_act\<close>

lemma pa_act_c_unchanged:
  assumes "pa_act N i (c, p) = (c', p')"
  shows "c = c'"
  using assms apply (cases "(N, i, (c, p))" rule: pa_act.cases)
  by auto

lemma pa_act_init_p_unchanged:
  assumes "pa_act N i (c, p) = (c', p')"
    and "c = CoInit"
  shows "p = p'"
  using assms apply (cases "(N, i, (c, p))" rule: pa_act.cases)
  by auto

lemma pa_act_c_wait_unchanged:
  assumes "pa_act N i s = s'"
    and "x < N"
    and "fst s = CoWait"
    and "(snd s) x = PaInit \<or> (snd s) x = PaReady \<or> (snd s) x = PaAbort "
  shows "(snd s') x = PaInit \<or> (snd s') x = PaReady \<or> (snd s') x = PaAbort"
  using assms apply (cases "(N, i, s)" rule: pa_abort.cases)
  by (auto split: if_splits)

lemma pa_act_commit_p_unchanged:
  assumes "pa_act N i (c, p) = (c', p')"
    and "c = CoCommit"
    and "x < N"
    and "p x = PaCommit \<or> p x = PaReady"
  shows "p' x = PaCommit \<or> p' x = PaReady"
  using assms apply (cases "(N, i, (c, p))" rule: pa_act.cases)
  by (auto split: if_splits)

lemma pa_act_abort_p_unchanged:
  assumes "pa_act N i s = s'"
    and "fst s = CoAbort"
    and "x < N"
    and "(snd s) x = PaInit \<or> (snd s) x = PaReady \<or> (snd s) x = PaAbort"
  shows "(snd s') x = PaInit \<or> (snd s') x = PaReady \<or> (snd s') x = PaAbort"
  using assms apply (cases "(N, i, s)" rule: pa_act.cases)
  by (auto split: if_splits)

subsection \<open>pa_abort\<close>

lemma pa_abort_c_unchanged:
  assumes "pa_abort N i (c, p) = (c', p')"
  shows "c = c'"
  using assms apply (cases "(N, i, (c, p))" rule: pa_abort.cases)
  by (auto split: if_splits)

lemma pa_abort_p_abort_unchanged:
  assumes "pa_abort N i (c, p) = (c', p')"
    and "x < N"
    and "p x = PaInit \<or> p x = PaAbort"
  shows "p' x = PaInit \<or> p' x = PaAbort"
  using assms apply (cases "(N, i, (c, p))" rule: pa_abort.cases)
  by (auto split: if_splits)

lemma pa_abort_p_init_ready_abort_unchanged:
  assumes "pa_abort N i s = s'"
    and "x < N"
    and "(snd s) x = PaInit \<or> (snd s) x = PaAbort \<or> (snd s) x = PaReady"
  shows "(snd s') x = PaInit \<or> (snd s') x = PaAbort \<or> (snd s') x = PaReady "
  using assms apply (cases "(N, i, s)" rule: pa_abort.cases)
  by (auto split: if_splits)

lemma pa_abort_p_commit_ready_unchanged:
  assumes "pa_abort N i (c, p) = (c', p')"
    and "x < N"
    and "p x = PaCommit \<or> p x = PaReady"
  shows "p' x = PaCommit \<or> p' x = PaReady"
  using assms apply (cases "(N, i, (c, p))" rule: pa_abort.cases)
  by (auto split: if_splits)


subsection \<open>co_timeout\<close>

lemma co_timeout_CoInit:
  assumes "co_timeout (c, p) = (c', p')"
    and "c' = CoInit"
  shows "c = CoInit"
  using assms apply (cases "((c, p))" rule: co_timeout.cases)
  by auto

lemma co_timeout_p_unchanged:
  assumes "co_timeout (c, p) = (c', p')"
  shows "p = p'"
  using assms apply (cases "((c, p))" rule: co_timeout.cases)
  by auto

lemma co_timeout_CoWait:
  assumes "co_timeout (c, p) = (c', p')"
    and "c' = CoWait"
  shows "c = CoWait"
  using assms apply (cases "((c, p))" rule: co_timeout.cases)
  by auto

lemma co_timeout_CoAbort:
  assumes "co_timeout (c, p) = (c', p')"
    and "c' = CoAbort"
  shows "c = CoWait \<or> c = CoAbort"
  using assms apply (cases "((c, p))" rule: co_timeout.cases)
  by auto

section \<open>lemmas of progress\<close>

lemma aborts_commits_abort[simp]:
  "aborts_commits (c', ps(i := PaAbort)) = aborts_commits (c, ps) \<union> {i}"
  by auto

lemma aborts_commits_commit[simp]:
  "aborts_commits (c', ps(i := PaCommit)) = aborts_commits (c, ps) \<union> {i}"
  by auto

lemma aborts_commits_progress1[simp]:
  assumes "aborts_commits s \<union> {i} = aborts_commits s'"
  shows "progress s \<le> progress s'"
  using assms 
  by (metis Un_insert_right card_insert_le progress.elims sup_bot_right)

lemma aborts_commits_progress2[simp]:
  assumes "aborts_commits s = aborts_commits s'"
  shows "progress s \<le> progress s'"
  using assms
  by (metis order_refl progress.elims)

lemma co_abort_unchanged:
  assumes "co_abort s = s'"
  shows "aborts_commits s = aborts_commits s'"
  by (metis aborts_commits.elims assms co_abort_p_unchanged)

lemma co_commit_unchanged:
  assumes "co_commit s = s'"
  shows "aborts_commits s = aborts_commits s'"
  by (metis aborts_commits.elims assms co_commit_p_unchanged)

lemma co_timeout_unchanged:
  assumes "co_timeout s = s'"
  shows "aborts_commits s = aborts_commits s'"
  by (metis aborts_commits.elims assms co_timeout_p_unchanged)

lemma co_act_unchanged:
  assumes "co_act N s = s'"
  shows "aborts_commits s = aborts_commits s'"
  by (metis aborts_commits.elims assms co_act_p_unchanged)

lemma pa_act_progress:
  assumes "pa_act N i s = s'"
  shows "aborts_commits s \<union> {i} = aborts_commits s'
      \<or> aborts_commits s = aborts_commits s'"
proof (cases "(N, i, s)" rule: pa_act.cases)
  case (1 N i ps)
  then show ?thesis proof (cases "ps i = PaInit")
    case True
    have "i \<notin> aborts_commits s"
      using "1" True by auto
    have "i \<notin> aborts_commits s'"
      using "1" True assms by force
    have "\<forall>x \<in> aborts_commits s. x \<in> aborts_commits s'"
      using "1" assms by force
    then show ?thesis
      by (smt (z3) "1" Collect_cong Pair_inject aborts_commits.simps assms fun_upd_other 
          fun_upd_same mem_Collect_eq pa_act.simps(1) pa_state.distinct(7) pa_state.distinct(9))
  next
    case False
    then show ?thesis
      using "1" assms by auto
  qed
next
  case (2 N i ps)
  then show ?thesis 
    using assms by force
next
  case (3 N i ps)
  then show ?thesis 
    using assms by force
next
  case (4 N i ps)
  then show ?thesis 
    using assms by force
qed

lemma pa_abort_progress:
  assumes "pa_abort N i s = s'"
  shows "aborts_commits s \<union> {i} = aborts_commits s'
      \<or> aborts_commits s = aborts_commits s'"
    by (metis aborts_commits_abort assms pa_abort.simps prod.collapse)

section "Two-Phase Commit: Phase 1"

text \<open>Before coordinator prepares to commit, all participants must be in PaInit or PaAbort 
(participants might abort because of transaction failure)\<close>

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
  have "fst s = CoInit"
    by (metis "4.hyps"(2) "4.prems"(1) co_act_CoInit eq_fst_iff)
  then have "snd s x = PaInit \<or> snd s x = PaAbort"
    by (simp add: "4.IH" "4.prems"(2))
  then show ?case 
    by (metis "4.hyps"(2) co_act_p_unchanged prod.exhaust_sel)
next
  case (5 s N s')
  have fst_init5: "fst s = CoInit"
    by (metis "5.hyps"(3) "5.prems"(1) pa_act_c_unchanged prod.exhaust_sel)
  then have "snd s x = PaInit \<or> snd s x = PaAbort"
    by (simp add: "5.IH" "5.prems"(2))
  then show ?case 
    by (metis "5.hyps"(3) fst_init5 pa_act.simps(4) prod.exhaust_sel)
next
  case (6 s N x s')
  have "fst s = CoInit"
    by (metis "6.hyps"(3) "6.prems"(1) pa_abort_c_unchanged prod.exhaust_sel)
  then have "snd s x = PaInit \<or> snd s x = PaAbort"
    by (simp add: "6.IH" "6.prems"(2))
  then show ?case
    by (metis "6.hyps"(3) "6.prems"(2) pa_abort_p_abort_unchanged prod.exhaust_sel)
next
  case (7 s N s')
  have "fst s = CoInit"
    by (metis "7.hyps"(2) "7.prems"(1) co_timeout_CoInit prod.collapse)
  then have "snd s x = PaInit \<or> snd s x = PaAbort"
    using "7.IH" "7.prems"(2) by blast
  then show ?case
    by (metis "7.hyps"(2) co_timeout_p_unchanged prod.exhaust_sel)
qed

corollary safety_co_init:
  assumes "valid_sys (c, ps) N"
    and "c = CoInit"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states (ps x) (ps y)"
  by (metis assms(1) assms(2) assms(3) assms(4) co_init_pa_init_or_abort 
      consistent_pa_states.elims(3) fst_conv pa_state.distinct(3) pa_state.simps(12) snd_conv)

text \<open>Before coordinator decides, participants might abort because of 
transaction failure, but must not commit.\<close>

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
  have "fst s = CoWait"
    by (metis "2.hyps"(2) "2.prems"(1) co_abort_CoWait prod.exhaust_sel)
  have "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
    using "2.IH" "2.prems"(2) \<open>fst s = CoWait\<close> by blast
  then show ?case 
    by (metis "2.hyps"(2) co_abort_p_unchanged prod.exhaust_sel)
next
  case (3 s N s')
  have fst_case: "fst s = CoInit \<or> fst s = CoWait"
    by (metis "3.hyps"(2) "3.prems"(1) co_commit_CoWait surjective_pairing)
  from fst_case show ?case 
  proof
    assume "fst s = CoInit"
    then show "snd s' x = PaInit \<or> snd s' x = PaAbort \<or> snd s' x = PaReady" 
      by (metis "3.hyps"(1) "3.hyps"(2) "3.prems"(2) co_commit.simps(1) 
          co_init_pa_init_or_abort split_pairs)
  next
    assume "fst s = CoWait"
    then have "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
      using "3.IH" "3.prems"(2) by presburger
    then show "snd s' x = PaInit \<or> snd s' x = PaAbort \<or> snd s' x = PaReady"
      by (metis "3.hyps"(2) co_commit_p_unchanged prod.collapse)
  qed 
next
  case (4 s N s')
  have "fst s = CoWait"
    by (metis "4.hyps"(2) "4.prems"(1) co_act_CoWait prod.exhaust_sel)
  then have "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
    using "4.IH" "4.prems"(2) by presburger
  then show ?case 
    by (metis "4.hyps"(2) co_act_p_unchanged prod.exhaust_sel)
next
  case (5 s N i s')
  have "fst s = CoWait"
    by (metis "5.hyps"(3) "5.prems"(1) pa_act_c_unchanged prod.exhaust_sel)
  then have hypo_con: "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
    using "5.IH" "5.prems"(2) by presburger
  then show ?case
    using "5.hyps"(3) "5.prems"(2) \<open>fst s = CoWait\<close> pa_act_c_wait_unchanged by blast
next
  case (6 s N i s')
  have "fst s = CoWait"
    by (metis "6.hyps"(3) "6.prems"(1) pa_abort_c_unchanged surjective_pairing)
  then have hypo_con: "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
    using "6.IH" "6.prems"(2) by presburger
  then show ?case 
    by (simp add: "6.hyps"(3) "6.prems"(2) pa_abort_p_init_ready_abort_unchanged)
next
  case (7 s N s')
  have "fst s = CoWait"
    by (metis "7.hyps"(2) "7.prems"(1) co_timeout_CoWait surjective_pairing)
  then have hypo_con: "snd s x = PaInit \<or> snd s x = PaAbort \<or> snd s x = PaReady"
    using "7.IH" "7.prems"(2) by presburger
  then show ?case
    by (metis "7.hyps"(2) co_timeout_p_unchanged prod.exhaust_sel)
qed

corollary safety_co_wait:
  assumes "valid_sys (c, ps) N"
    and "c = CoWait"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states (ps x) (ps y)"
  by (metis assms(1) assms(2) assms(3) assms(4) co_wait_pa_init_or_abort_or_ready 
      consistent_pa_states.elims(3) fst_conv pa_state.distinct(3) pa_state.distinct(7) 
      pa_state.simps(12) snd_conv)

section \<open>Two-Phase Commit: Phase 2\<close>

text \<open>Once coordinator decides to commit, participants must be in PaCommit or PaReady\<close>

lemma co_commit_pa_commit_or_ready:
  assumes "valid_sys s N"
    and "fst s = CoCommit"
    and "x < N"
  shows "(snd s) x = PaCommit \<or> (snd s) x = PaReady"
using assms proof (induction s N arbitrary: x rule: valid_sys.induct)
  case (1 N)
  then show ?case
    by (simp add: init_def)
next
  case (2 s N s')
  have "fst s = CoCommit"
    by (metis "2.hyps"(2) "2.prems"(1) co_abort_CoCommit prod.exhaust_sel)
  then have "(snd s) x = PaCommit \<or> (snd s) x = PaReady"
    by (simp add: "2.IH" "2.prems"(2))
  then show ?case
    by (metis "2.hyps"(2) co_abort_p_unchanged prod.collapse)
next
  case (3 s N s')
  have "fst s = CoCommit"
    by (metis "3.hyps"(2) "3.prems"(1) co_commit_CoCommit surjective_pairing)
  then have "(snd s) x = PaCommit \<or> (snd s) x = PaReady"
    by (simp add: "3.IH" "3.prems"(2))
  then show ?case 
    by (metis "3.hyps"(2) co_commit_p_unchanged prod.collapse)
next
  case (4 s N s')
  have fst_case: "fst s = CoCommit \<or> fst s = CoWait"
    by (metis "4.hyps"(2) "4.prems"(1) co_act_CoCommit prod.exhaust_sel)
  from fst_case show ?case 
  proof
    assume "fst s = CoCommit"
    then show "snd s' x = PaCommit \<or> snd s' x = PaReady" 
      by (metis "4.IH" "4.hyps"(2) "4.prems"(2) co_act.simps(3) fst_conv surj_pair)
  next
    assume "fst s = CoWait"
    then show "snd s' x = PaCommit \<or> snd s' x = PaReady"
      by (metis "4.hyps"(2) "4.prems"(1) "4.prems"(2) co_act_transition_no_init prod.collapse)
  qed
next
  case (5 s N s')
  have fst_commit: "fst s = CoCommit"
    by (metis "5.hyps"(3) "5.prems"(1) pa_act_c_unchanged prod.exhaust_sel)
  then have "(snd s) x = PaCommit \<or> (snd s) x = PaReady"
    by (simp add: "5.IH" "5.prems"(2))
  then show ?case 
    by (metis "5.hyps"(3) "5.prems"(2) fst_commit pa_act_commit_p_unchanged surjective_pairing)
next
  case (6 s N x s')
  then show ?case 
    by (metis pa_abort.simps pa_state.distinct(1) pa_state.distinct(3) split_pairs)
next
  case (7 s N s')
  then show ?case
    by (metis Pair_inject co_state.simps(12) co_timeout.elims prod.exhaust_sel)
qed


corollary safety_co_commit:
  assumes "valid_sys (c, ps) N"
    and "c = CoCommit"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states (ps x) (ps y)"
  by (metis assms(1) assms(2) assms(3) assms(4) co_commit_pa_commit_or_ready 
      consistent_pa_states.elims(3) fst_conv pa_state.distinct(9) pa_state.simps(12) snd_conv)


text \<open>Once coordinator decides to abort, participants must not commit\<close>

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
  have fst_case: "fst s = CoAbort \<or> fst s = CoInit"
    by (metis "2.hyps"(2) "2.prems"(1) co_abort_CoAbort prod.exhaust_sel)
  from fst_case show ?case
  proof 
    assume "fst s = CoAbort" 
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort"
      by (metis "2.IH" "2.hyps"(2) "2.prems"(2) co_abort.simps(4) prod.collapse)
  next
    assume "fst s = CoInit"
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort"
      by (metis "2.hyps"(1) "2.hyps"(2) "2.prems"(2) co_abort.simps(1) 
          co_init_pa_init_or_abort split_pairs)
  qed
next
  case (3 s N s')
  have "fst s = CoAbort"
    by (metis "3.hyps"(2) "3.prems"(1) co_commit_CoAbort prod.collapse)
  then have "snd s x = PaInit \<or> snd s x = PaReady \<or> snd s x = PaAbort"
    using "3.IH" "3.prems"(2) by blast
  then show ?case 
    by (metis "3.hyps"(2) co_commit_p_unchanged prod.exhaust_sel)
next
  case (4 s N s')
  have fst_case: "fst s = CoAbort \<or> fst s = CoWait"
    by (metis "4.hyps"(2) "4.prems"(1) co_act_CoAbort prod.exhaust_sel)
  from fst_case show ?case 
  proof
    assume "fst s = CoAbort"
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort" 
      by (metis "4.IH" "4.hyps"(2) "4.prems"(2) co_act_p_unchanged prod.exhaust_sel)
  next
    assume "fst s = CoWait"
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort"
      by (metis "4.hyps"(1) "4.hyps"(2) "4.prems"(2) co_act_p_unchanged 
          co_wait_pa_init_or_abort_or_ready prod.exhaust_sel)
  qed
next
  case (5 s N s')
  have "fst s = CoAbort"
    by (metis "5.hyps"(3) "5.prems"(1) pa_act_c_unchanged prod.exhaust_sel)
  then have "snd s x = PaInit \<or> snd s x = PaReady \<or> snd s x = PaAbort"
    using "5.IH" "5.prems"(2) by blast
  then show ?case 
    by (simp add: "5.hyps"(3) "5.prems"(2) \<open>fst s = CoAbort\<close> pa_act_abort_p_unchanged)
next
  case (6 s N x s')
  have "fst s = CoAbort"
    by (metis "6.hyps"(3) "6.prems"(1) pa_abort_c_unchanged surjective_pairing)
  then have "snd s x = PaInit \<or> snd s x = PaReady \<or> snd s x = PaAbort"
    using "6.IH" "6.prems"(2) by blast
  then show ?case 
    using "6.hyps"(3) "6.prems"(2) pa_abort_p_init_ready_abort_unchanged by blast
next
  case (7 s N s')
  have fst_case: "fst s = CoWait \<or> fst s = CoAbort"
    by (metis "7.hyps"(2) "7.prems"(1) co_timeout_CoAbort prod.exhaust_sel)
  from fst_case show ?case 
  proof
    assume "fst s = CoWait"
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort"
      by (metis "7.hyps"(1) "7.hyps"(2) "7.prems"(2) co_timeout.simps(1) 
        co_wait_pa_init_or_abort_or_ready prod.collapse snd_conv)
  next
    assume "fst s = CoAbort"
    then show "snd s' x = PaInit \<or> snd s' x = PaReady \<or> snd s' x = PaAbort"
      by (metis "7.IH" "7.hyps"(2) "7.prems"(2) co_timeout.simps(4) prod.collapse)
  qed
qed
  
corollary safety_co_abort:
  assumes "valid_sys (c, ps) N"
    and "c = CoAbort"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states (ps x) (ps y)"
  by (metis assms(1) assms(2) assms(3) assms(4) co_abort_pa_init_or_ready_abort 
      consistent_pa_states.elims(3) fst_conv pa_state.distinct(3) pa_state.distinct(7) 
      pa_state.simps(12) snd_conv)

section \<open>Two-Phase Commit: Correctness\<close>

subsection \<open>Safety\<close>

theorem safety:
  assumes "valid_sys (c, ps) N"
    and "x < N"
    and "y < N"
  shows "consistent_pa_states (ps x) (ps y)"
  using assms safety_co_init safety_co_wait safety_co_commit safety_co_abort 
  by (cases "c") auto

subsection \<open>Liveness\<close>

lemma liveness_co_abort:
  assumes "valid_sys s N"
    and "co_abort s = s'"
  shows "progress s' \<ge> progress s"
  using aborts_commits_progress2 assms(2) co_abort_unchanged by blast

lemma liveness_co_commit:
  assumes "valid_sys s N"
    and "co_commit s = s'"
  shows "progress s' \<ge> progress s"
  using aborts_commits_progress2 assms(2) co_commit_unchanged by blast

lemma liveness_co_timeout:
  assumes "valid_sys s N"
    and "co_timeout s = s'"
  shows "progress s' \<ge> progress s"
  using aborts_commits_progress2 assms(2) co_timeout_unchanged by blast

lemma liveness_co_act:
  assumes "valid_sys s N"
    and "co_act N s = s'"
  shows "progress s' \<ge> progress s"
  using aborts_commits_progress2 assms(2) co_act_unchanged by blast

lemma liveness_pa_abort:
  assumes "valid_sys s N"
    and "pa_abort N i s = s'"
  shows "progress s' \<ge> progress s"
  by (metis aborts_commits_progress1 aborts_commits_progress2 assms(2) pa_abort_progress)

lemma liveness_pa_act:
  assumes "valid_sys s N"
    and "pa_act N i s = s'"
  shows "progress s' \<ge> progress s"
  by (metis aborts_commits_progress1 aborts_commits_progress2 assms(2) pa_act_progress)
  

end
