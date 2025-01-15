(*
  Full source available at: https://github.com/talemke/IMP-TuringComplete
  Depends on projects from the AFP: https://www.isa-afp.org/help/
*)

section\<open>Introduction\<close>

subsection\<open>Background\<close>

text\<open>
  When investigating different models of computation, we often are interested in their
  expressiveness and powerfulness, that is determining which type of computations can be done.
  By a long-standing claim of Church and Turing we, to this day, believe that the most powerful
  machines we can have, are those that can perform every a computation a Turing-Machine can compute as well.
  \<^cite>\<open>"Copeland1997"\<close>
  The most interesting question we can thus pose about a computational model,
  is whether it is \textit{Turing-Complete} or not.
  That is, is the model capable of computing everything a Turing-Machine can compute.
  The most common approach is to either show, that a model can simulate any Turing-Machine,
  or that it can simulate a specific Turing-Machine: the Universal Turing Machine.
  \<^cite>\<open>"Turing1937"\<close>
\<close>

subsection\<open>Motivation\<close>

text\<open>
  \textit{IMP} is a ``minimalistic imperative programming language'' introduced by Nipkow and Klein
  in their works of formalising programming language semantics.
  \<^cite>\<open>"Nipkow2014"\<close>
  Altough it is claimed to be Turing-Complete, a formal proof of this fact is not of my knowledge.
  Therefore, in this project, we attempt to fully prove the Turing-Completeness of IMP.
\<close>

subsection\<open>Proof Sketch\<close>

text\<open>
  Since the definition of Turing-Machines we use only requires two state symbols ($Bk$ and $Oc$),
  we can make use of a binary representation to encode tapes, where $0$ represents the blank symbol $Bk$,
  while $1$ represents the other symbol $Oc$.
  That two state symbols are sufficient to simulate any Turing-Machine, given enough states,
  has already been shown by Claude E. Shannon in 1956.\<^cite>\<open>"Shannon1956"\<close>
\<close>

text\<open>
  This is also beneficial, as it allows us to represent an infinite tape, without having to deal with actual infinite data structures,
  since a natural number has an infinite amount of zeroes in its binary representation in theory.
  Pushing and reading from the tape can then be achieved using only multiplication by two,
  integer-division by two and its remainder.
\<close>

text\<open>
  We will later construct an IMP-program that stores the infinite tapes to the left and right in two variables,
  and uses two more variables to store the current state and head.
  The IMP-program will then repeat until it reaches a final state,
  executing the next transition of the Turing-Machine with each step.
\<close>

text\<open>
  We can then show that when the IMP-program terminates, its variables represent the same configuration
  the ``normal'' Turing-Machine would have when it would terminate.
\<close>

subsection\<open>Dependencies\<close>

text\<open>
  We use the Hoare Logic for both Partial and Total Correctness of IMP to prove our constructed program correct.
  Furthermore, we take an existing definition of Turing-Machines from the AFP\<^cite>\<open>"Universal_Turing_Machine-AFP"\<close>,
  although we will create a slightly different intermediate definition later on.
\<close>

theory IMP_TuringComplete
  imports
    "HOL-IMP.Hoare_Total"
    "HOL-IMP.Hoare_Sound_Complete"
    "Universal_Turing_Machine.Turing_aux"
begin \<comment>\<open>begin-theory IMP\_TuringComplete\<close>

text\<open>
  During the time of writing, the Hoare Logic was the most powerful and latest introduced tool
  for reasoning about semantics of my knowledge.
  There are surely ways to make some proofs shorter and more elegant.
  However, I took it as a challenge and exercise to use a Hoare Logic and only it,
  meaning also no Verification Condition Generation.
\<close>

section\<open>Intermediate Representation\<close>

text\<open>
  The imported definition of Turing-Machines defines a tape-configuration slightly differently than usual,
  deviating from the standard 3-tuple $(L, H, R)$, containing the infinite tape to the left and right
  and the current head symbol, by only using the 2-tuple $(L, R)$, where the head symbol is the first
  symbol on the right tape.
\<close>

text\<open>
  While this definition may seem to make next to no difference,
  we will save us much trouble by defining an intermediate representation using the standard 3-tuple right away.
  Furthermore, we will directly encode the infinite tapes to the left and right as natural numbers,
  which will make our definition both more well-defined, see section \ref{ch:tape-eq},
  and make some later proofs easier.
\<close>

subsection\<open>Tape Translation\<close>

subsubsection\<open>Defining Tape Equivalence \label{ch:tape-eq}\<close>

text\<open>
  The definition of Turing-Machines in the ``Universal Turing Machine''\<^cite>\<open>"Universal_Turing_Machine-AFP"\<close>
  project allows for inherently ambiguous tapes (namely having trailing blanks).
  Since the tapes have infinite trailing blanks in theory,
  this effectively means that the standard $=$ relation is insufficient.
  \newline

  Because of this, we define a custom equality relation $=_T$,
  which specifies the equality of the tape contents.
  To make things easier for us later, we also define a custom equality relation $=_C$,
  which specifies the equality of an entire TM-configuration.
\<close>

fun tape_eq :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" (infix "=\<^sub>T" 55) where
  "((x#xs) =\<^sub>T (y#ys)) = ((x = y) \<and> (xs =\<^sub>T ys))" |
  "((x#xs) =\<^sub>T []) = ((x = Bk) \<and> (xs =\<^sub>T []))" |
  "([] =\<^sub>T (y#ys)) = ((y = Bk) \<and> ([] =\<^sub>T ys))" |
  "([] =\<^sub>T []) = True"

fun config_eq :: "config \<Rightarrow> config \<Rightarrow> bool" (infix "=\<^sub>C" 55) where
  "((s1, l1, r1) =\<^sub>C (s2, l2, r2)) = ((s1 = s2) \<and> (l1 =\<^sub>T l2) \<and> (r1 =\<^sub>T r2))"

lemma tape_eq_correct:
  assumes "xs =\<^sub>T ys"
  shows "read xs = read ys" and "tl xs =\<^sub>T tl ys"
  using assms by (induction xs ys rule: tape_eq.induct) simp+

text\<open>
  \textbf{Future Note}:
  Given the latest lecture I am now convinced a much more elegant solution for this
  would have been to use equivalence classes and/or a quotient datatype.
  Sadly, during the time of writing I was not aware of this feature,
  which now introduces this rather complicated custom equivalence relation.
\<close>

text\<open>
  We now prove some generic properties of the equality relation,
  namely reflexivity, symmetry and transitivity.
\<close>

lemma tape_eq_refl: "xs =\<^sub>T xs"
  by (induction xs) simp+

lemma config_eq_refl: "(s, l, r) =\<^sub>C (s, l, r)"
  using tape_eq_refl by simp

lemma config_eq_refl': "c =\<^sub>C c"
  using prod_cases3 config_eq_refl by metis

lemma tape_eq_sym: "xs =\<^sub>T ys \<Longrightarrow> ys =\<^sub>T xs"
  by (induction xs ys rule: tape_eq.induct) simp+

lemma config_eq_sym: "(s1, l1, r1) =\<^sub>C (s2, l2, r2) \<Longrightarrow> (s2, l2, r2) =\<^sub>C (s1, l1, r1)"
  using tape_eq_sym by simp

lemma config_eq_sym': "c1 =\<^sub>C c2 \<Longrightarrow> c2 =\<^sub>C c1"
  using prod_cases3 config_eq_sym by metis

lemma tape_eq_trans: "xs =\<^sub>T ys \<Longrightarrow> ys =\<^sub>T zs \<Longrightarrow> xs =\<^sub>T zs"
proof (induction xs zs arbitrary: ys rule: tape_eq.induct)
  case (1 x xs z zs)
  then show ?case by (induction ys) force+
next
  case (2 x xs)
  then show ?case by (induction ys) force+
next
  case (3 z zs)
  then show ?case by (induction ys) force+
next
  case 4
  then show ?case by simp
qed

lemma config_eq_trans:
  assumes "(s1, l1, r1) =\<^sub>C (s2, l2, r2)"
    and "(s2, l2, r2) =\<^sub>C (s3, l3, r3)"
  shows "(s1, l1, r1) =\<^sub>C (s3, l3, r3)"
  using assms tape_eq_trans[of l1 l2 l3] tape_eq_trans[of r1 r2 r3] by simp

lemma config_eq_trans': "c1 =\<^sub>C c2 \<Longrightarrow> c2 =\<^sub>C c3 \<Longrightarrow> c1 =\<^sub>C c3"
  using prod_cases3 config_eq_trans by metis

subsubsection\<open>Translation: Tape $\Longleftrightarrow$ Natural Numbers\<close>

text\<open>
  We want to use natural numbers, specifically their binary representation, to encode tapes.
  This has the benefit of uniquely identifying tapes, since theoretically the binary
  representations also have an infinite number of zeroes (the blank symbol).
\<close>

text\<open>
  Using the binary representation means shifting the tape is as simple as multiplying or
  dividing by $2$, to extract the top element we can use modulo $2$.
\<close>

fun cell_to_nat :: "cell \<Rightarrow> nat" where
  "cell_to_nat Bk = 0" |
  "cell_to_nat Oc = 1"

fun nat_to_cell :: "nat \<Rightarrow> cell" where
  "nat_to_cell 0 = Bk" |
  "nat_to_cell n = Oc"

fun tape_to_nat :: "cell list \<Rightarrow> nat" where
  "tape_to_nat (x#xs) = 2 * tape_to_nat xs + (cell_to_nat x)" |
  "tape_to_nat [] = 0"

lemma tape_to_nat_det:
  assumes "xs =\<^sub>T ys"
  shows "tape_to_nat xs = tape_to_nat ys"
  using assms by (induction xs ys rule: tape_eq.induct) simp+

fun nat_to_tape :: "nat \<Rightarrow> cell list" where
  "nat_to_tape 0 = []" |
  "nat_to_tape n = (nat_to_cell (n mod 2))#(nat_to_tape (n div 2))"

subsubsection\<open>Tape Operations\<close>

text\<open>
  We can now prove that multiplication, division and modulo behave as expected.
\<close>

lemma mul2_is_push_bk:
  assumes "nat_to_tape n =\<^sub>T xs"
  shows "nat_to_tape (2*n) =\<^sub>T (Bk#xs)"
  using assms by (cases n) simp+

lemma mul2_is_push_oc:
  assumes "nat_to_tape n =\<^sub>T xs"
  shows "nat_to_tape (2*n + 1) =\<^sub>T (Oc#xs)"
  using assms by simp

lemma mul2_is_push:
  assumes "nat_to_tape n =\<^sub>T xs"
  shows "nat_to_tape (2*n + cell_to_nat x) =\<^sub>T (x#xs)"
proof (cases x)
  case Bk thus ?thesis by (simp add: assms mul2_is_push_bk)
next
  case Oc thus ?thesis by (simp add: assms mul2_is_push_oc)
qed

lemma div2_is_pop:
  assumes "nat_to_tape n =\<^sub>T xs"
  shows "nat_to_tape (n div 2) =\<^sub>T tl xs"
proof (cases "n \<noteq> 0")
  case True
  then have "nat_to_tape n \<noteq> []"
    using nat_to_tape.elims by blast
  then obtain y ys where ys_def: "(y#ys) = nat_to_tape n"
    by (metis nat_to_tape.elims)
  then have "ys =\<^sub>T tl xs"
    by (metis assms list.collapse list.sel(2) tape_eq.simps(1) tape_eq.simps(2))
  moreover have "ys = nat_to_tape (n div 2)"
    by (metis ys_def True list.inject nat_to_tape.elims)
  ultimately show ?thesis
    by simp
next
  case False
  with assms show ?thesis by (cases xs) (use tape_eq.simps in simp)+
qed

lemma mod2_is_read:
  assumes "nat_to_tape n =\<^sub>T xs"
  shows "nat_to_cell (n mod 2) = read xs"
proof (cases "n \<noteq> 0")
  case True
  then have "nat_to_tape n \<noteq> []"
    using nat_to_tape.elims by blast
  then obtain y ys where ys_def: "(y#ys) = nat_to_tape n"
    by (metis nat_to_tape.elims)
  then have "read xs = y"
  proof (cases xs)
    case Nil
    then have "(y#ys) =\<^sub>T []"
      using assms ys_def by simp
    then show ?thesis
      using tape_eq.simps(2) Nil by simp
  next
    case (Cons x xs)
    then have "(y#ys) =\<^sub>T (x#xs)"
      using assms ys_def by simp
    then show ?thesis
      using tape_eq.simps(1)[of y ys x xs] Cons by simp
  qed
  moreover have "nat_to_cell (n mod 2) = y"
    by (metis ys_def True list.inject nat_to_tape.elims)
  ultimately show ?thesis by simp
next
  case False
  with assms show ?thesis by (cases xs) (use tape_eq.simps in simp)+
qed

lemma nat_to_cell_ident: "n < 2 \<Longrightarrow> cell_to_nat (nat_to_cell n) = n"
  by (induction n rule: nat_to_cell.induct) simp+

lemma cell_to_nat_ident: "nat_to_cell (cell_to_nat c) = c"
  by (cases c) simp+

lemma nat_to_tape_ident: "tape_to_nat (nat_to_tape n) = n"
  by (induction n rule: nat_to_tape.induct) (use nat_to_cell_ident in simp)+

lemma tape_to_nat_ident: "nat_to_tape (tape_to_nat xs) =\<^sub>T xs"
proof (induction xs rule: tape_to_nat.induct)
  case (1 x xs)
  then show ?case by (cases x) (simp add: mul2_is_push_bk)+
next
  case 2
  then show ?case by simp
qed

lemma tape_to_nat_ident_read: "nat_to_cell ((tape_to_nat xs) mod 2) = read xs"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs)
  then show ?thesis by (cases x) simp+
qed

lemma tape_to_nat_ident_tl: "nat_to_tape ((tape_to_nat xs) div 2) =\<^sub>T tl xs"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs)
  then show ?thesis by (cases x) (use tape_to_nat_ident in simp)+
qed

lemma tape_eq_merge: "r' =\<^sub>T tl r \<Longrightarrow> read r = h \<Longrightarrow> h#r' =\<^sub>T r"
  by (cases r) simp+

lemma tape_eq_merge2: "r \<noteq> [] \<Longrightarrow> hd r # nat_to_tape (tape_to_nat (tl r)) =\<^sub>T r"
  by (simp add: tape_eq_merge tape_to_nat_ident)

subsection\<open>Intermediate State\<close>

text\<open>
  Our intermediate-tape is a 3-tuple $(L, H, R)$, where:
  \begin{itemize}
    \item $L$ is the infinite tape to the left, represented as a natural number
    \item $R$ is the inifnite tape to the right, represented as a natural number
    \item $H$ is the symbol at the current head
  \end{itemize}
\<close>
type_synonym itape = "nat \<times> cell \<times> nat"

text\<open>
  The complete intermediate-state is then a 4-tuple $(S, L, H, R)$, where:
  \begin{itemize}
    \item $S$ is the current state of the TM
    \item $(L, H, R)$ is the intermediate-tape, as described above
  \end{itemize}
\<close>
type_synonym istate = "state \<times> itape"

fun config_to_istate :: "config \<Rightarrow> istate" where
  "config_to_istate (s, l, r) = (s, tape_to_nat l, read r, tape_to_nat (tl r))"

lemma config_to_istate_det:
  assumes "(s1, l1, r1) =\<^sub>C (s2, l2, r2)"
  shows "config_to_istate (s1, l1, r1) = config_to_istate (s2, l2, r2)"
proof -
  let ?s1 = "(s1, l1, r1)"
  let ?s2 = "(s2, l2, r2)"

  obtain s1' l1' h1' r1' where st1_def: "(s1', l1', h1', r1') = config_to_istate ?s1"
    by simp
  obtain s2' l2' h2' r2' where st2_def: "(s2', l2', h2', r2') = config_to_istate ?s2"
    by simp

  have "s1 = s2"
    using assms by simp
  then have s_eq: "s1' = s2'"
    using st1_def st2_def by simp

  have "l1 =\<^sub>T l2"
    using assms by simp
  then have l_eq: "l1' = l2'"
    using st1_def st2_def by (simp add: tape_to_nat_det)

  have "r1 =\<^sub>T r2"
    using assms by simp
  moreover have "tl r1 =\<^sub>T tl r2"
    using tape_eq_correct calculation by simp
  ultimately have h_eq: "h1' = h2'" and r_eq: "r1' = r2'"
    using tape_eq_correct tape_to_nat_det st1_def st2_def by simp+

  from s_eq l_eq h_eq r_eq show ?thesis
    using st1_def st2_def by simp
qed

lemma config_to_istate_det':
  assumes "c1 =\<^sub>C c2"
  shows "config_to_istate c1 = config_to_istate c2"
  using assms prod_cases3 config_to_istate_det by metis

fun istate_to_config :: "istate \<Rightarrow> config" where
  "istate_to_config (s, l, h, r) = (s, nat_to_tape l, h#(nat_to_tape r))"

lemma config_to_istate_ident: "istate_to_config (config_to_istate (s, l, r)) =\<^sub>C (s, l, r)"
  by (simp add: tape_to_nat_ident tape_eq_merge2)

lemma config_to_istate_ident': "istate_to_config (config_to_istate c) =\<^sub>C c"
  using prod_cases3 config_to_istate_ident by metis

lemma istate_to_config_ident: "config_to_istate (istate_to_config (s, l, h, r)) = (s, l, h, r)"
  by (simp add: nat_to_tape_ident)

lemma istate_to_config_ident': "config_to_istate (istate_to_config st) = st"
  using prod_cases3 istate_to_config_ident by metis

lemma istate_to_config_l: "istate_to_config (s, l, h, r) = (s', l', r') \<Longrightarrow> nat_to_tape l =\<^sub>T l'"
  using config_eq_refl by simp

lemma istate_to_config_r: "istate_to_config (s, l, h, r) = (s', l', r') \<Longrightarrow> nat_to_tape r =\<^sub>T tl r'"
  using config_eq_refl by (cases r') simp+

lemma istate_to_config_h: "istate_to_config (s, l, h, r) = (s', l', r') \<Longrightarrow> h = read r'"
  by (cases r') simp+

lemma istate_to_config_s: "istate_to_config (s, l, h, r) = (s', l', r') \<Longrightarrow> s = s'"
  by simp

subsection\<open>Single-Step Execution\<close>

fun iupdate :: "instr \<Rightarrow> istate \<Rightarrow> istate" where
  "iupdate (WB, s') (s, l, h, r) = (s', l, Bk, r)" |
  "iupdate (WO, s') (s, l, h, r) = (s', l, Oc, r)" |
  "iupdate (L, s') (s, l, h, r) = (s', l div 2, nat_to_cell (l mod 2), 2*r + cell_to_nat h)" |
  "iupdate (R, s') (s, l, h, r) = (s', 2*l + cell_to_nat h, nat_to_cell (r mod 2), r div 2)" |
  "iupdate (Nop, s') (s, l, h, r) = (s', l, h, r)"

lemma iupdate_correct:
  assumes "(s', l', h', r') = config_to_istate (s, l, r)"
  shows "istate_to_config (iupdate (a, s'') (s', l', h', r')) =\<^sub>C (s'', update a (l, r))"
proof (cases a)
  case WB
  then show ?thesis by (simp add: assms tape_to_nat_ident)
next
  case WO
  then show ?thesis by (simp add: assms tape_to_nat_ident)
next
  case L
  then have "iupdate (a, s'') (s', l', h', r') = (s'', l' div 2, nat_to_cell (l' mod 2), 2*r' + cell_to_nat h')"
    by simp
  moreover have "(s'', update a (l, r)) = (s'', tl l, (read l)#r)"
    using L by (cases l) simp+
  moreover have "nat_to_tape (l' div 2) =\<^sub>T tl l"
    using assms by (simp add: tape_to_nat_ident div2_is_pop)
  moreover have "nat_to_tape (2*r' + cell_to_nat h') =\<^sub>T h'#(tl r)"
    using assms by (simp add: tape_to_nat_ident mul2_is_push)
  moreover have "h'#(tl r) =\<^sub>T r"
    using assms by (simp add: tape_eq_refl)
  moreover have "nat_to_tape (2*r' + cell_to_nat h') =\<^sub>T r"
    using calculation(4) calculation(5) tape_eq_trans by blast
  ultimately show ?thesis
    using assms by (simp add: mod2_is_read tape_to_nat_ident)
next
  case R
  then have "iupdate (a, s'') (s', l', h', r') = (s'', 2*l' + cell_to_nat h', nat_to_cell (r' mod 2), r' div 2)"
    by simp
  moreover have "(s'', update a (l, r)) = (s'', (read r)#l, tl r)"
    using R by (cases r) simp+
  moreover have "nat_to_tape (r' div 2) =\<^sub>T tl (tl r)"
    using assms by (simp add: tape_to_nat_ident div2_is_pop)
  moreover have "nat_to_tape (2*l' + cell_to_nat h') =\<^sub>T h'#l"
    using assms by (simp add: tape_to_nat_ident mul2_is_push)
  moreover have "h'#l =\<^sub>T (read r)#l"
    using assms by (simp add: tape_eq_refl)
  moreover have "nat_to_tape (2*l' + cell_to_nat h') =\<^sub>T (read r)#l"
    using calculation(4) calculation(5) tape_eq_trans by blast
  moreover have "(nat_to_cell (r' mod 2))#nat_to_tape (r' div 2) =\<^sub>T tl r"
    using calculation(3) assms tape_to_nat_ident_read tape_to_nat_ident_tl tape_eq_merge by simp
  ultimately show ?thesis
    using assms by simp
next
  case Nop
  then show ?thesis by (simp add: assms tape_to_nat_ident tape_eq_merge)
qed

lemma config_eq_det_is_final:
  assumes "(s1, l1, r1) =\<^sub>C (s2, l2, r2)"
  shows "is_final (s1, l1, r1) = is_final (s2, l2, r2)"
  using assms by simp

lemma config_eq_det_is_final': "c1 =\<^sub>C c2 \<Longrightarrow> is_final c1 = is_final c2"
  using config_eq_det_is_final prod_cases3 by metis

subsection\<open>Correct-Step Execution\<close>

subsubsection\<open>Instruction-Index\<close>

text\<open>
  The UTM project we use as dependency executes step, by calculating an instruction index.
  Turing-Machines are represented as lists of instructions and the corresponding instruction
  is then executed.
\<close>

text\<open>
  The original calculation of this index is:
  $$i := 2s + h$$
  where $s$ is the current state and $h$ is the current head symbol ($0$ for $Bk$, $1$ for $Oc$).
\<close>

fun istate_to_index :: "istate \<Rightarrow> nat" where
  "istate_to_index (s, l, h, r) = 2*s + cell_to_nat h"

abbreviation config_to_index :: "config \<Rightarrow> nat" where
  "config_to_index c \<equiv> istate_to_index (config_to_istate c)"

text\<open>
  When executing the corresponding instruction, the UTM project first checks if we are in
  a final state, and would short-circuit to execute a $Nop$ instruction.
  However, we avoid this short-circuiting by calculating the real instruction index.
  If it were a final state ($s = 0$), the resulting index would be $0$ or $1$.
  Thereby, we simply ``prepend'' two $Nop$ instructions to the Turing-Machine.
  The actual implementation is a bit different and more ugly, by actually checking the value,
  however the behavior is semantically identical.
\<close>

abbreviation load_instr :: "tprog0 \<Rightarrow> nat \<Rightarrow> instr" (infix "@\<^sub>I" 55) where
  "tm @\<^sub>I i \<equiv> (if i < (2 + length tm) \<and> i \<ge> 2 then tm!(i-2) else (Nop, 0))"

lemma load_instr_correct:
  "tm @\<^sub>I (istate_to_index (s, l, h, r)) = fetch tm s h"
proof (induction tm s h rule: fetch.induct)
  case (1 p b)
  then show ?case by (cases b) simp+
next
  case (2 p s)
  then show ?case by simp
next
  case (3 p s)
  then show ?case by simp
qed

subsubsection\<open>Instruction Execution\<close>

text\<open>
  We now define step functions on our intermediate-state.
  Furthermore, we can prove that the instruction-index as explained above works as epxected.
\<close>

fun istep :: "tprog0 \<Rightarrow> istate \<Rightarrow> istate" where
  "istep tm (s, l, h, r) = iupdate (fetch tm s h) (s, l, h, r)"

lemma istep_eq:
  "istep tm (s, l, h, r) = iupdate (tm @\<^sub>I (istate_to_index (s, l, h, r))) (s, l, h, r)"
  using load_instr_correct by simp

lemma istep_index_skip:
  assumes "istate_to_index (s, l, h, r) \<ge> 2 + (length tm)"
  shows "istep tm (s, l, h, r) = (0, l, h, r)"
  using assms istep_eq by simp

lemma istep_index_skip':
  assumes "istate_to_index st \<ge> 2 + (length tm)"
  shows "istep tm st = iupdate (Nop, 0) st"
  using assms istep_index_skip prod_cases4 iupdate.simps(5) by metis

lemma istep_index_correct:
  assumes "istate_to_index (s, l, h, r) < 2 + (length tm)"
  shows "istep tm (s, l, h, r) = iupdate (tm @\<^sub>I (istate_to_index (s, l, h, r))) (s, l, h, r)"
  using assms istep_eq by simp

lemma istep_index_correct':
  assumes "istate_to_index st < 2 + (length tm)"
  shows "istep tm st = iupdate (tm @\<^sub>I (istate_to_index st)) st"
proof -
  obtain s l h r where "st = (s, l, h, r)"
    using prod_cases4 by blast
  then show ?thesis
    using assms istep_index_correct by simp
qed

lemma istep_correct:
  assumes "(s1, l1, r1) \<Turnstile>\<langle>tm\<rangle>\<Midarrow> (s2, l2, r2)"
  shows "istep tm (config_to_istate (s1, l1, r1)) = config_to_istate (s2, l2, r2)"
proof -
  let ?s1 = "(s1, l1, r1)"
  let ?s2 = "(s2, l2, r2)"

  obtain s1' l1' h1' r1' where st1_def: "(s1', l1', h1', r1') = config_to_istate ?s1"
    by simp
  obtain s2' l2' h2' r2' where st2_def: "(s2', l2', h2', r2') = config_to_istate ?s2"
    by simp

  let ?st1 = "(s1', l1', h1', r1')"
  let ?st2 = "(s2', l2', h2', r2')"

  obtain i1 where i1_def: "i1 = fetch tm s1 (read r1)"
    by simp
  obtain i2 where i2_def: "i2 = tm @\<^sub>I istate_to_index ?st1"
    by simp
  have "read r1 = h1'" and "s1 = s1'"
    using st1_def by simp+
  with i1_def i2_def have "i1 = i2"
    using load_instr_correct by simp

  obtain a s' where "i1 = (a, s')" and "i2 = (a, s')"
    using \<open>i1 = i2\<close> by fastforce

  have "step0 ?s1 tm = ?s2"
    using assms by (simp add: tm_step0_rel_def)
  then have a1: "?s2 = (s', update a (l1, r1))"
    using i1_def \<open>i1 = (a, s')\<close> by force

  have a2: "istep tm ?st1 = iupdate i2 ?st1"
    using i2_def istep_eq by simp

  have "istate_to_config (iupdate i2 ?st1) =\<^sub>C (s', update a (l1, r1))"
    using iupdate_correct st1_def \<open>i1 = i2\<close> \<open>i2 = (a, s')\<close> by simp
  then have "istate_to_config (istep tm ?st1) =\<^sub>C ?s2"
    using a1 a2 by simp
  then have "config_to_istate (istate_to_config (istep tm ?st1)) = config_to_istate ?s2"
    using config_to_istate_det' by simp
  then have "istep tm (config_to_istate ?s1) = config_to_istate ?s2"
    using st1_def istate_to_config_ident' by simp
  then show ?thesis .
qed

lemma istep_correct':
  assumes "c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c2"
  shows "istep tm (config_to_istate c1) = config_to_istate c2"
  using assms istep_correct prod_cases3 by metis

lemma config_eq_step0:
  assumes "c1 =\<^sub>C c2"
  shows "step0 c1 tm =\<^sub>C step0 c2 tm"
proof -
  have "config_to_istate c1 = config_to_istate c2"
    using config_to_istate_det' assms by simp
  then obtain s where s_def1: "s = config_to_istate c1"
      and s_def2: "s = config_to_istate c2"
    by simp

  obtain c1' where c1'_def: "c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c1'"
    by (simp add: tm_step0_rel_def)
  then have step1: "istep tm s = config_to_istate c1'"
    using s_def1 istep_correct' by simp
  
  obtain c2' where c2'_def: "c2 \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c2'"
    by (simp add: tm_step0_rel_def)
  then have step2: "istep tm s = config_to_istate c2'"
    using s_def2 istep_correct' by simp

  have "config_to_istate c1' = config_to_istate c2'"
    using step1 step2 by simp
  then have "c1' =\<^sub>C c2'"
    by (metis config_to_istate_ident' config_eq_trans' config_eq_sym')
  with c1'_def c2'_def show ?thesis
    by (simp add: tm_step0_rel_def)
qed

lemma config_eq_steps0: "c1 =\<^sub>C c2 \<Longrightarrow> steps0 c1 tm n =\<^sub>C steps0 c2 tm n"
  by (induction n) (use config_eq_step0 in simp)+

section\<open>Constructing the IMP-Program\<close>

text\<open>
  We now have a sufficient foundation to start constructing the IMP-program,
  that will later simulate an arbitrary Turing-Machine.
\<close>

subsection\<open>Translation: Intermediate State $\Longleftrightarrow$ IMP-State\<close>

text\<open>
  First, we need to establish a mapping between our previously defined intermediate-state
  and an IMP-state.
  An IMP-state is mapping $vname \to int$ of variables to their values.
  Our IMP-program will need no more than five variables:
\<close>

\<comment>\<open>Stores the current state.\<close>
abbreviation "vnS \<equiv> ''tm_state''"

\<comment>\<open>Stores the current head symbol.\<close>
abbreviation "vnH \<equiv> ''tm_head''"

\<comment>\<open>Stores the infinite tape to left.\<close>
abbreviation "vnL \<equiv> ''tm_left''"

\<comment>\<open>Stores the infinite tape to right.\<close>
abbreviation "vnR \<equiv> ''tm_right''"

\<comment>\<open>This is a utility variable, which doesn't store any additional information,
  but will later be used as an index to execute the correct step.\<close>
abbreviation "vnSI \<equiv> ''tm_state_index''"

type_synonym impstate = "AExp.state"

text\<open>
  Having this distinction of variables makes some proofs later a bit easier,
  but introduces the problem of invalid states.
  For example, the tapes are encoded as natural numbers, but the variables can have any integer,
  including negative numbers.
\<close>

text\<open>
  To preserve a unique and valid state, we introduce an invariant,
  which ensures the variables we use have a proper value.
\<close>

abbreviation impstate_inv :: "impstate \<Rightarrow> bool" where
  "impstate_inv s \<equiv> (s vnS \<ge> 0 \<and> (s vnH = 0 \<or> s vnH = 1) \<and> s vnL \<ge> 0 \<and> s vnR \<ge> 0)"

text\<open>
  Finally, we can define the translation between IMP-states and our intermediate-states:
\<close>

\<comment>\<open>We allow an arbitrary intial state here, which defines the values of all other variables.\<close>
abbreviation istate_to_impstate :: "impstate \<Rightarrow> istate \<Rightarrow> impstate" where
  "istate_to_impstate b st \<equiv> (
    let (s, l, h, r) = st in
    b (vnS := int s, vnH := int (cell_to_nat h), vnL := int l, vnR := int r)
  )"

abbreviation impstate_to_istate :: "impstate \<Rightarrow> istate" where
  "impstate_to_istate s \<equiv> (nat (s vnS), nat (s vnL), nat_to_cell (nat (s vnH)), nat (s vnR))"

text\<open>
  It can be shown, that every possible intermediate-state will always map to an IMP-state,
  that satisfies our previously defined invariant:
\<close>

lemma istate_to_impstate_inv: "impstate_inv (istate_to_impstate b st)"
proof -
  obtain s l h r where "st = (s, l, h, r)"
    using prod_cases4 by blast
  then show ?thesis
    by (cases h) simp+
qed

text\<open>
  Furthermore, we can also show that our translation is bijective:
\<close>

lemma istate_to_impstate_ident: "impstate_to_istate (istate_to_impstate b st) = st"
proof -
  obtain s l h r where "st = (s, l, h, r)"
    using prod_cases4 by blast
  then show ?thesis
    by (cases h) simp+
qed

text\<open>
  Using the previously established mapping between TM-configurations and intermediate-states,
  and the now defined mapping between intermediate-states and IMP-states,
  we finally define the chained mapping between TM-configurations and IMP-states:
\<close>

abbreviation config_to_impstate :: "impstate \<Rightarrow> config \<Rightarrow> impstate" where
  "config_to_impstate s c \<equiv> istate_to_impstate s (config_to_istate c)"

abbreviation impstate_to_config :: "impstate \<Rightarrow> config" where
  "impstate_to_config s \<equiv> istate_to_config (impstate_to_istate s)"

subsection\<open>Utility Programs\<close>

text\<open>
  Now we can start constructing some smaller utility IMP-programs,
  which will slowly allow us to build the final IMP-program.
\<close>

text\<open>
  The arithmetic instructions provided by IMP are limited (only supporting addition),
  we will however construct programs to compute both multiplication by two
  and integer-division by two and its remainder, and prove them correct.
\<close>

subsubsection\<open>A Generalization for Hoare-Logic\<close>

text\<open>
  First, we establish some facts about our Hoare logic, which will help us with some proofs later.
\<close>

text\<open>
  It is often much easier to prove that a program modifies a state in a given way $t$,
  such that if the starting state is $s_0$, the final state will be $t(s_0)$.
  However, making use of this is rather cumbersome.
  It is much easier to have the same statement, but with two predicates $f$ and $g$,
  such that if $f$ holds for every initial state $s$, then $g$ also holds for $t(s)$,
  then $f$ is valid pre-condition and $g$ is a valid post-condition for the program.
  This allows us to insert arbitrary predicates and use the previously established fact of
  a fixed starting state $s_0$ much more easily.
\<close>

lemma hoare_generalize:
  assumes "\<And>s\<^sub>0. \<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} c {\<lambda>s. s = t s\<^sub>0}"
    and "\<And>s. f s \<Longrightarrow> g (t s)"
  shows "\<turnstile>\<^sub>t {f} c {g}"
proof -
  have "\<And>s\<^sub>0. \<forall>s. s = s\<^sub>0 \<longrightarrow> (\<exists>s'. (c,s) \<Rightarrow> s' \<and> t s\<^sub>0 = s')"
    using hoare_tvalid_def hoaret_sound_complete assms(1) by simp
  then have "\<And>s. (c,s) \<Rightarrow> t s"
    by simp
  then have "\<forall>s. f s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> g t)"
    using assms(2) by blast
  then show ?thesis
    using hoare_tvalid_def hoaret_sound_complete by simp
qed

text\<open>
  While this formulation works well for most cases, it has a limitation:
  we have no assertion about the initial states to begin with.
  But sometimes we have proved statements about an initial state $s_0$,
  while posing some assumptions about it.
  To allow for this, we have to modify the above lemma a bit,
  by also asserting that the pre-condition $f$ will only hold,
  if the assumptions posed on $s_0$ are also met.
\<close>

lemma hoare_generalize':
  assumes "\<And>s\<^sub>0. a s\<^sub>0 \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} c {\<lambda>s. s = t s\<^sub>0}"
    and "\<And>s. f s \<Longrightarrow> g (t s)" and "\<And>s. f s \<Longrightarrow> a s"
  shows "\<turnstile>\<^sub>t {f} c {g}"
proof -
  have "\<And>s\<^sub>0. a s\<^sub>0 \<Longrightarrow> \<forall>s. s = s\<^sub>0 \<longrightarrow> (\<exists>s'. (c,s) \<Rightarrow> s' \<and> t s\<^sub>0 = s')"
    using hoare_tvalid_def hoaret_sound_complete assms(1) by simp
  then have "\<And>s. a s \<Longrightarrow> (c,s) \<Rightarrow> t s"
    by simp
  then have "\<forall>s. f s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> g t)"
    using assms(2) assms(3) by blast
  then show ?thesis
    using hoare_tvalid_def hoaret_sound_complete by simp
qed

text\<open>
  We now define two basic facts, which directly follow from the rules of the Hoare logic.
  However, we swapped the order of assumption, which makes proof automation easier later on.
\<close>

lemma Seq': "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3}; \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"
  by (simp only: Seq)

lemma conseq': "\<turnstile>\<^sub>t {P} c {Q} \<Longrightarrow> \<forall>s. P' s \<longrightarrow> P s \<Longrightarrow> \<forall>s. Q s \<longrightarrow> Q' s \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q'}"
  by (simp only: conseq)

lemma partial_conseq': "\<turnstile> {P} c {Q} \<Longrightarrow> \<forall>s. P' s \<longrightarrow> P s \<Longrightarrow> \<forall>s. Q s \<longrightarrow> Q' s \<Longrightarrow> \<turnstile> {P'} c {Q'}"
  by (simp only: hoare.conseq)

text\<open>
  Another scenario we will encounter occasionally is where we have a pre-condition,
  which always will be False.
  We define two lemmas, which will make automating such scenarios rather easily,
  by only having to show that $P$ is always False.
\<close>

lemma hoare_FalseI: "\<turnstile>\<^sub>t {\<lambda>s. False} c {Q}"
  by (simp add: hoaret_sound_complete hoare_tvalid_def)

lemma hoare_Contr: "\<forall>s. P' s \<longrightarrow> False \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
  by (rule strengthen_pre; use hoare_FalseI in blast)

subsubsection\<open>Multiplication by 2\<close>

text\<open>
  First, we construct a program \texttt{mul2}, which performs a multiplication by two:
  $$mul2 \; a \; b \quad \to \quad b \; := \; 2*a$$
  This can be computed in a single step, by simply taking the sum of $a$ and $a$ again.
\<close>

definition "mul2 a b \<equiv> (b ::= (Plus (V a) (V a)))"

text\<open>
  A proof of total-correctness is pretty straight-forward.
\<close>

lemma mul2_correct:
  assumes "\<And>s. f s \<Longrightarrow> g (s (b := 2 * (s a)))"
  shows "\<turnstile>\<^sub>t {f} (mul2 a b) {g}"
  unfolding mul2_def by (rule Assign', use assms in simp)

lemma mul2_correct': "\<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} (mul2 a b) {\<lambda>s. s = s\<^sub>0 (b := 2 * (s\<^sub>0 a))}"
  unfolding mul2_def by (rule Assign', simp)

subsubsection\<open>Integer-Division by 2\<close>

text\<open>
  Next, we construct a program \texttt{moddiv2}, which performs integer-division by two,
  retrieving both the quotient and the remainder:
  $$moddiv2 \; a \; q \; m \quad \to \quad q \; := \; a \; div \; 2, \; m \; := \; a \; mod \; 2$$
  Constructing such a program is bit more tedious and involves continuously subtracting
  in a WHILE-loop.
  The primitive version we implement also only works for positive numbers,
  however since our IMP-state invariant ensures that relevant variables are always positive,
  this is sufficient for our case.
\<close>

definition "moddiv2_setup a q m \<equiv> (
  m ::= (V a) ;;
  q ::= (N 0)
)"

lemma moddiv2_setup_correct':
  assumes "q \<noteq> m"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} moddiv2_setup a q m {\<lambda>s. s = s\<^sub>0 (q := 0, m := s\<^sub>0 a)}"
  unfolding moddiv2_setup_def
  by (rule Seq'; rule Assign') (use assms in force)+

lemma moddiv2_setup_correct:
  assumes "q \<noteq> m" and "\<And>s. f s \<Longrightarrow> g (s (q := 0, m := s a))"
  shows "\<turnstile>\<^sub>t {f} moddiv2_setup a q m {g}"
proof -
  let ?t = "\<lambda>s. s (q := 0, m := s a)"
  from assms moddiv2_setup_correct' show ?thesis
    using hoare_generalize[where t="?t"] by blast
qed

definition "moddiv2_step q m \<equiv> (
    m ::= Plus (V m) (N (-2)) ;;
    q ::= Plus (V q) (N 1)
)"

lemma moddiv2_step_correct':
  assumes "q \<noteq> m"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} moddiv2_step q m {\<lambda>s. s = s\<^sub>0 (q := s\<^sub>0 q + 1, m := s\<^sub>0 m - 2)}"
  unfolding moddiv2_step_def
  by (rule Seq'; rule Assign') (use assms in force)+

lemma moddiv2_step_correct:
  assumes "q \<noteq> m" and "\<And>s. f s \<Longrightarrow> g (s (q := s q + 1, m := s m - 2))"
  shows "\<turnstile>\<^sub>t {f} moddiv2_step q m {g}"
proof -
  let ?t = "\<lambda>s. s (q := s q + 1, m := s m - 2)"
  from assms moddiv2_step_correct' show ?thesis
    using hoare_generalize[where t="?t"] by blast
qed

definition "moddiv2_loop q m \<equiv> (
  WHILE Less (N 1) (V m) DO (
    moddiv2_step q m
  )
)"

definition "moddiv2 a q m \<equiv> (
  moddiv2_setup a q m ;;
  moddiv2_loop q m
)"

lemma moddiv2_correct':
  assumes "q \<noteq> m" and "s\<^sub>0 a \<ge> 0"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s = s\<^sub>0} moddiv2 a q m {\<lambda>s. s = s\<^sub>0 (q := s\<^sub>0 a div 2, m := s\<^sub>0 a mod 2)}"
proof -
  let ?P = "\<lambda>s. s = s\<^sub>0"
  let ?P' = "\<lambda>s. \<exists>q' m'. s = s\<^sub>0 (q := q', m := m') \<and> s\<^sub>0 a = 2*q' + m' \<and> q' \<ge> 0 \<and> m' \<ge> 0"
  let ?Q = "\<lambda>s. s = s\<^sub>0 (q := s\<^sub>0 a div 2, m := s\<^sub>0 a mod 2)"

  let ?f = "\<lambda>n. \<lambda>s. ?P' s \<and> bval (Less (N 1) (V m)) s \<and> n = nat (s m)"
  let ?g = "\<lambda>n. \<lambda>s. ?P' s \<and> nat (s m) < n"
  have step: "\<And>n::nat. \<turnstile>\<^sub>t {?f n} moddiv2_step q m {?g n}"
  proof -
    fix n :: nat
    have "\<And>s. ?f n s \<Longrightarrow> ?g n (s (q := s q + 1, m := s m - 2))"
      using assms by fastforce
    then show "\<turnstile>\<^sub>t {?f n} moddiv2_step q m {?g n}"
      using assms(1) moddiv2_step_correct by presburger
  qed

  have loop_body: "\<turnstile>\<^sub>t {?P'} moddiv2_loop q m {?Q}"
    unfolding moddiv2_loop_def
    by (rule While_fun'[where f="\<lambda>s. nat (s m)"], use step in auto)

  have loop_setup: "\<turnstile>\<^sub>t {?P} moddiv2_setup a q m {?P'}"
    unfolding moddiv2_setup_def
    by (rule Seq'; rule Assign') (use assms in force)+

  show ?thesis
    unfolding moddiv2_def
    by (rule Seq; use loop_setup loop_body in simp)
qed

lemma moddiv2_correct:
  assumes "q \<noteq> m"
    and "\<And>s. f s \<Longrightarrow> g (s (q := s a div 2, m := s a mod 2))"
    and "\<And>s. f s \<Longrightarrow> s a \<ge> 0"
  shows "\<turnstile>\<^sub>t {f} (moddiv2 a q m) {g}"
proof -
  let ?a = "\<lambda>s. s a \<ge> 0"
  let ?t = "\<lambda>s. s (q := s a div 2, m := s a mod 2)"
  from assms moddiv2_correct' show ?thesis
    using hoare_generalize'[where a="?a" and t="?t"] by blast
qed

subsubsection\<open>List-Index Program\<close>

\<comment>\<open>Two shorthands for testing two variables for equivalence.\<close>
abbreviation "eq a b \<equiv> And (Not (Less a b)) (Not (Less b a))"
abbreviation "neq a b \<equiv> Not (eq a b)"

text\<open>
  Next, we need to construct a program that simulates a (non-fallthrough) \texttt{SWITCH}-statement.
  Precisely, we construct a program \texttt{list\_index\_prog}, that takes in a variable name,
  a list of programs and a fallback program, and constructs a new program that uses the provided
  variable to index the program-list and execute the right one, or execute the fallback program
  if the index is out of bounds.
\<close>

text\<open>
  Constructing the program in a way, that doesn't change the variables
  (e.g. by subtracting one from the index at every step),
  requires us to introduce an index-offset:
\<close>

fun list_index_prog' :: "vname \<Rightarrow> int \<Rightarrow> com list \<Rightarrow> com \<Rightarrow> com" where
  "list_index_prog' vn n (p#ps) e = (
    IF eq (V vn) (N n) THEN p
    ELSE list_index_prog' vn (n+1) ps e
  )" |
  "list_index_prog' vn n [] e = e"

text\<open>
  We can now prove that our program with index-offset works as expected,
  by executing the program at the index or the fallback program.
  Proving this requires delicate use of induction, but then yields a proper proof:
\<close>

lemma list_index_prog'_skip:
  assumes "i \<ge> length ps"
    and "\<turnstile>\<^sub>t {P} e {Q}"
  shows "\<turnstile>\<^sub>t {\<lambda>s. P s \<and> s vn = n + int i} list_index_prog' vn n ps e {Q}"
using assms proof (induction vn n ps e arbitrary: i rule: list_index_prog'.induct)
  \<comment>\<open>We still are checking indices:\<close>
  \<comment>\<open>Show that they mismatch and continue with induction.\<close>
  case (1 vn n p ps e)

  let ?TP' = "\<lambda>s. P s \<and> s vn = n + int i \<and> bval (eq (V vn) (N n)) s"
  have "\<forall>s. ?TP' s \<longrightarrow> False"
    using 1(2) by simp
  moreover have "\<turnstile>\<^sub>t {\<lambda>s. False} p {Q}"
    using hoare_FalseI by simp
  ultimately have TrueCase: "\<turnstile>\<^sub>t {?TP'} p {Q}"
    using strengthen_pre[where P="\<lambda>s. False" and P'="?TP'"] by simp

  let ?FP = "\<lambda>s. P s \<and> s vn = n + 1 + int (i - 1)"
  let ?FP' = "\<lambda>s. P s \<and> s vn = n + int i \<and> \<not> bval (eq (V vn) (N n)) s"
  have "length ps \<le> i - 1"
    using 1(2) by simp
  then have "\<turnstile>\<^sub>t {?FP} list_index_prog' vn (n + 1) ps e {Q}"
    using 1(1)[of "i-1"] 1(3) by simp
  moreover have "\<forall>s. ?FP' s \<longrightarrow> ?FP s"
    by fastforce
  ultimately have FalseCase: "\<turnstile>\<^sub>t {?FP'} list_index_prog' vn (n + 1) ps e {Q}"
    using strengthen_pre[where P="?FP" and P'="?FP'"] by simp

  from list_index_prog'.simps(1) show ?case
    using TrueCase FalseCase by (simp add: If)
next
  \<comment>\<open>Index is out of bounds, finally execute the fallback.\<close>
  case (2 vn n e)

  let ?P' = "\<lambda>s. P s \<and> s vn = n + int i"
  have "\<forall>s. ?P' s \<longrightarrow> P s"
    by simp
  with 2 show ?case
    using conseq[where P'="?P'" and P="P"] by simp
qed

lemma list_index_prog'_correct:
  assumes "i < length ps"
    and "\<turnstile>\<^sub>t {P} ps!i {Q}"
  shows "\<turnstile>\<^sub>t {\<lambda>s. P s \<and> s vn = n + int i} list_index_prog' vn n ps e {Q}"
using assms proof (induction vn n ps e arbitrary: i rule: list_index_prog'.induct)
  case (1 vn n p ps e)
  let ?P = "\<lambda>s. P s \<and> s vn = n + int i"
  show ?case proof (cases "i = 0")
    \<comment>\<open>Index match! Execute our branch.\<close>
    case True

    let ?TP = "\<lambda>s. ?P s \<and> bval (eq (V vn) (N n)) s"
    have "\<forall>s. ?TP s \<longrightarrow> P s"
      by simp
    moreover have "\<turnstile>\<^sub>t {P} p {Q}"
      using 1(3) True by simp
    ultimately have TrueCase: "\<turnstile>\<^sub>t {?TP} p {Q}"
      using strengthen_pre[where P="P" and P'="?TP"] by simp
  
    let ?FP = "\<lambda>s. ?P s \<and> \<not> bval (eq (V vn) (N n)) s"
    have "\<forall>s. ?FP s \<longrightarrow> False"
      using True by simp
    moreover have "\<turnstile>\<^sub>t {\<lambda>s. False} list_index_prog' vn (n + 1) ps e {Q}"
      using hoare_FalseI by simp
    ultimately have FalseCase: "\<turnstile>\<^sub>t {?FP} list_index_prog' vn (n + 1) ps e {Q}"
      using strengthen_pre[where P="\<lambda>s. False" and P'="?FP"] by simp

    from list_index_prog'.simps(1) show ?thesis
      using TrueCase FalseCase by (simp add: If)
  next
    \<comment>\<open>Index mismatch, continue with induction.\<close>
    case False

    let ?TP = "\<lambda>s. ?P s \<and> bval (eq (V vn) (N n)) s"
    have "\<forall>s. ?TP s \<longrightarrow> False"
      using False by simp
    moreover have "\<turnstile>\<^sub>t {\<lambda>s. False} p {Q}"
      using hoare_FalseI by simp
    ultimately have TrueCase: "\<turnstile>\<^sub>t {?TP} p {Q}"
      using strengthen_pre[where P="\<lambda>s. False" and P'="?TP"] by simp

    let ?FP = "\<lambda>s. ?P s \<and> \<not> bval (eq (V vn) (N n)) s"
    let ?FP' = "\<lambda>s. P s \<and> s vn = n + 1 + int (i - 1)"
    have "i - 1 < length ps"
      using 1(2) False by simp
    moreover have "\<turnstile>\<^sub>t {P} ps ! (i - 1) {Q}"
      using 1(3) False by simp
    ultimately have "\<turnstile>\<^sub>t {?FP'} list_index_prog' vn (n + 1) ps e {Q}"
      using 1(1) by simp
    moreover have "\<forall>s. ?FP s \<longrightarrow> ?FP' s"
      by fastforce
    ultimately have FalseCase: "\<turnstile>\<^sub>t {?FP} list_index_prog' vn (n + 1) ps e {Q}"
      using strengthen_pre[where P="?FP'" and P'="?FP"] by simp

    from list_index_prog'.simps(1) show ?thesis
      using TrueCase FalseCase by (simp add: If)
  qed
next
  case (2 vn n)
  then show ?case by simp
qed

text\<open>
  The final \texttt{list\_index\_prog} program is now the above defined program,
  with an index-offset of $n=0$.
\<close>

definition list_index_prog :: "vname \<Rightarrow> com list \<Rightarrow> com \<Rightarrow> com" where
  "list_index_prog vn ps e = list_index_prog' vn 0 ps e"

text\<open>
  The same proofs for the final program now follow directly:
\<close>

corollary list_index_prog_skip:
  assumes "i \<ge> length ps" and "\<turnstile>\<^sub>t {P} e {Q}"
  shows "\<turnstile>\<^sub>t {\<lambda>s. P s \<and> s vn = int i} list_index_prog vn ps e {Q}"
  unfolding list_index_prog_def
  using assms list_index_prog'_skip[where n=0] by simp

corollary list_index_prog_correct:
  assumes "i < length ps" and "\<turnstile>\<^sub>t {P} ps!i {Q}"
  shows "\<turnstile>\<^sub>t {\<lambda>s. P s \<and> s vn = int i} list_index_prog vn ps e {Q}"
  unfolding list_index_prog_def
  using assms list_index_prog'_correct[where n=0] by simp

subsection\<open>Operations\<close>

text\<open>
  We now start to construct programs that compute the possible Turing-Machine operations:
  \begin{itemize}
    \item $WB$: Write $Bk$ to head
    \item $WO$: Write $Oc$ to head
    \item $L$: Push head to right tape, pop left tape to head
    \item $R$: Push head to left tape, pop right tape to head
    \item $Nop$: Do nothing
  \end{itemize}
\<close>

text\<open>
  From now, we will encounter the following abbreviations in practically every proof.
  They both make statements about an IMP-state and ensure its invariant still holds.
  The first also states, that the IMP-state contains the same information as an intermediate-state,
  while the latter states, the IMP-state contains the same information as a TM-configuration.
\<close>

abbreviation impstate_to_istate_inv :: "impstate \<Rightarrow> istate \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>S" 55) where
  "s \<rightarrow>\<^sub>S st \<equiv> impstate_inv s \<and> impstate_to_istate s = st"

abbreviation impstate_to_config_inv :: "impstate \<Rightarrow> config \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>C" 55) where
  "s \<rightarrow>\<^sub>C c \<equiv> impstate_inv s \<and> (impstate_to_config s =\<^sub>C c)"

text\<open>
  We now show some useful rules about the abbreviations.
\<close>

text\<open>
  An important fact is that, although we have defined our abbreviation to be a relation,
  it actually still works almost like a function, in terms that its output is determined.
  A state can at most represent one configuration.
  However due to ambigiuous definition as explained in section \ref{ch:tape-eq},
  it doesn't imply real equivalence, but only our custom $=_C$ equivalence relation.
  \label{lem:impstate_to_config_inv_det}
\<close>

lemma impstate_to_config_inv_det:
  assumes "s \<rightarrow>\<^sub>C (s1, l1, r1)" and "s \<rightarrow>\<^sub>C (s2, l2, r2)"
  shows "(s1, l1, r1) =\<^sub>C (s2, l2, r2)"
  using assms config_eq_sym' config_eq_trans' by blast

lemma impstate_to_config_inv_det':
  assumes "s \<rightarrow>\<^sub>C c1" and "s \<rightarrow>\<^sub>C c2"
  shows "c1 =\<^sub>C c2"
proof -
  \<comment>\<open>For some reason a straight-forward metis proof would take too much time here.\<close>
  obtain s1 l1 r1 where c1_def: "c1 = (s1, l1, r1)"
    using prod_cases3 by blast
  obtain s2 l2 r2 where c2_def: "c2 = (s2, l2, r2)"
    using prod_cases3 by blast
  from c1_def c2_def show ?thesis
    using assms impstate_to_config_inv_det by blast
qed

lemma config_eq_implies_istate_eq:
  assumes "s \<rightarrow>\<^sub>C c"
  shows "s \<rightarrow>\<^sub>S config_to_istate c"
  using assms
proof -
  have "config_to_istate (impstate_to_config s) = impstate_to_istate s"
    using istate_to_config_ident' by blast
  moreover have "impstate_to_config s =\<^sub>C c"
    using assms by blast
  ultimately have "impstate_to_istate s = config_to_istate c"
    using config_to_istate_det'[of "impstate_to_config s"] by presburger
  thus ?thesis using assms by blast
qed

lemma config_eq_implies_istate_eq':
  assumes "s \<rightarrow>\<^sub>C istate_to_config st"
  shows "s \<rightarrow>\<^sub>S st"
  using assms
proof -
  obtain c where "s \<rightarrow>\<^sub>C c \<and> config_to_istate c = st"
    using assms istate_to_config_ident' by blast
  thus ?thesis using config_eq_implies_istate_eq by blast
qed

lemma istate_eq_implies_config_eq:
  assumes "s \<rightarrow>\<^sub>S config_to_istate c"
  shows "s \<rightarrow>\<^sub>C c"
  by (simp add: assms config_to_istate_ident')

lemma istate_eq_implies_config_eq':
  assumes "s \<rightarrow>\<^sub>S st"
  shows "s \<rightarrow>\<^sub>C istate_to_config st"
  by (simp add: assms config_eq_refl')

text\<open>
  With this foundation, we now construct a program for each of the possible TM-operations.
\<close>

subsubsection\<open>Write-Bk\<close>

definition prog_WB :: "state \<Rightarrow> com" where
  "prog_WB s \<equiv> (
    vnS ::= N (int s) ;;
    vnH ::= N (int (cell_to_nat Bk))
  )"

lemma prog_WB_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_WB st' {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (WB, st') (st, l, Bk, r)}"
  unfolding prog_WB_def by (rule Seq[where P\<^sub>2="\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)"]; rule Assign', simp)

subsubsection\<open>Write-Oc\<close>

definition prog_WO :: "state \<Rightarrow> com" where
  "prog_WO s \<equiv> (
    vnS ::= N (int s) ;;
    vnH ::= N (int (cell_to_nat Oc))
  )"

lemma prog_WO_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_WO st' {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (WO, st') (st, l, Oc, r)}"
  unfolding prog_WO_def by (rule Seq[where P\<^sub>2="\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)"]; rule Assign', simp)

subsubsection\<open>Move-Left\<close>

definition prog_L :: "state \<Rightarrow> com" where
  "prog_L s \<equiv> (
    vnS ::= N (int s) ;;
    mul2 vnR vnR ;;
    vnR ::= Plus (V vnR) (V vnH) ;;
    moddiv2 vnL vnL vnH
  )"

lemma prog_L_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_L st' {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (L, st') (st, l, h, r)}"
unfolding prog_L_def proof (rule Seq[where P\<^sub>2="\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)"])
  have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)}
    vnS ::= N (int st')
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)}"
    by (rule Assign', simp)
  moreover have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)}
    mul2 vnR vnR
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r)}"
  proof -
    let ?f = "\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)"
    let ?g = "\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r)"
    have "\<And>s. ?f s \<Longrightarrow> ?g (s (vnR := 2 * s vnR))" by force
    then show ?thesis using mul2_correct by presburger
  qed
  moreover have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r)}
    vnR ::= Plus (V vnR) (V vnH)
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)}"
    by (rule Assign', auto)
  ultimately show "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)}
    vnS ::= N (int st');; mul2 vnR vnR ;; vnR ::= Plus (V vnR) (V vnH)
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)}"
    using Seq by blast
next
  have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)}
    moddiv2 vnL vnL vnH
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l div 2, nat_to_cell (l mod 2), 2*r + cell_to_nat h)}"
  proof -
    let ?f = "\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)"
    let ?g = "\<lambda>s. s \<rightarrow>\<^sub>S (st', l div 2, nat_to_cell (l mod 2), 2*r + cell_to_nat h)"
    have "\<And>s. ?f s \<Longrightarrow> ?g (s (vnL := s vnL div 2, vnH := s vnL mod 2))"
    proof -
      fix s :: impstate
      assume "?f s"
      define s' where s'_def: "s' = s (vnL := s vnL div 2, vnH := s vnL mod 2)"

      from \<open>?f s\<close> have "s vnS = int st'"
        by force
      then have s'_st: "s' vnS = int st'" and "s' vnS \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have l_val: "s vnL = int l"
        by force
      then have s'_l: "s' vnL = int (l div 2)" and "s' vnL \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have r_val: "s vnR = int (2*r + cell_to_nat h)"
        by force
      then have s'_r: "s' vnR = int (2*r + cell_to_nat h)" and "s' vnR \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have "s vnH = int (cell_to_nat h)"
        by force
      then have s'_h: "s' vnH = int (l mod 2)"
        using s'_def l_val by (simp add: zmod_int)
      then have s'_h_invar: "s' vnH = 0 \<or> s' vnH = 1"
        by linarith

      have "?g s'"
        using s'_st s'_l s'_h s'_h_invar s'_r by simp
      then show "?g (s (vnL := s vnL div 2, vnH := s vnL mod 2))"
        using s'_def by blast
    qed
    then show ?thesis
      using moddiv2_correct by fastforce
  qed               
  then show "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, 2*r + cell_to_nat h)}
    moddiv2 vnL vnL vnH
    {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (L, st') (st, l, h, r)}"
    by simp
qed

subsubsection\<open>Move-Right\<close>

definition prog_R :: "state \<Rightarrow> com" where
  "prog_R s \<equiv> (
    vnS ::= N (int s) ;;
    mul2 vnL vnL ;;
    vnL ::= Plus (V vnL) (V vnH) ;;
    moddiv2 vnR vnR vnH
  )"

lemma prog_R_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_R st' {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (R, st') (st, l, h, r)}"
unfolding prog_R_def proof (rule Seq[where P\<^sub>2="\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)"])
  have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)}
    vnS ::= N (int st')
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)}"
    by (rule Assign', simp)
  moreover have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)}
    mul2 vnL vnL
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l, h,r)}"
  proof -
    let ?f = "\<lambda>s. s \<rightarrow>\<^sub>S (st', l, h, r)"
    let ?g = "\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l, h, r)"
    have "\<And>s. ?f s \<Longrightarrow> ?g (s (vnL := 2 * s vnL))" by force
    then show ?thesis using mul2_correct by presburger
  qed
  moreover have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l, h, r)}
    vnL ::= Plus (V vnL) (V vnH)
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)}"
    by (rule Assign', auto)
  ultimately show "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)}
    vnS ::= N (int st');; mul2 vnL vnL ;; vnL ::= Plus (V vnL) (V vnH)
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)}"
    using Seq by blast
next
  have "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)}
    moddiv2 vnR vnR vnH
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, nat_to_cell (r mod 2), r div 2)}"
  proof -
    let ?f = "\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)"
    let ?g = "\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, nat_to_cell (r mod 2), r div 2)"
    have "\<And>s. ?f s \<Longrightarrow> ?g (s (vnR := s vnR div 2, vnH := s vnR mod 2))"
    proof -
      fix s :: impstate
      assume "?f s"
      define s' where s'_def: "s' = s (vnR := s vnR div 2, vnH := s vnR mod 2)"

      from \<open>?f s\<close> have "s vnS = int st'"
        by force
      then have s'_st: "s' vnS = int st'" and "s' vnS \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have l_val: "s vnL = int (2*l + cell_to_nat h)"
        by force
      then have s'_l: "s' vnL = int (2*l + cell_to_nat h)" and "s' vnL \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have r_val: "s vnR = int r"
        by force
      then have s'_r: "s' vnR = int (r div 2)" and "s' vnR \<ge> 0"
        using s'_def by simp+

      from \<open>?f s\<close> have "s vnH = int (cell_to_nat h)"
        by force
      then have s'_h: "s' vnH = int (r mod 2)"
        using s'_def r_val by (simp add: zmod_int)
      then have s'_h_invar: "s' vnH = 0 \<or> s' vnH = 1"
        by linarith

      have "?g s'"
        using s'_st s'_l s'_h s'_h_invar s'_r by simp
      then show "?g (s (vnR := s vnR div 2, vnH := s vnR mod 2))"
        using s'_def by blast
    qed
    then show ?thesis
      using moddiv2_correct by fastforce
  qed
  then show "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S (st', 2*l + cell_to_nat h, h, r)}
    moddiv2 vnR vnR vnH
    {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (R, st') (st, l, h, r)}"
    by simp
qed

subsubsection\<open>No Operation\<close>

definition prog_Nop :: "state \<Rightarrow> com" where
  "prog_Nop s \<equiv> vnS ::= N (int s)"

lemma prog_Nop_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_Nop st' {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (Nop, st') (st, l, h, r)}"
  unfolding prog_Nop_def by (rule Assign', simp)

subsubsection\<open>Pattern-Matching Operation\<close>

text\<open>
  Now we can construct a pattern-matching wrapper,
  which provides the correct program, given a specific instruction.
\<close>

fun prog_step :: "instr \<Rightarrow> com" where
  "prog_step (WB, st) = prog_WB st" |
  "prog_step (WO, st) = prog_WO st" |
  "prog_step (L, st) = prog_L st" |
  "prog_step (R, st) = prog_R st" |
  "prog_step (Nop, st) = prog_Nop st"

text\<open>
  The proofs again follow directly.
\<close>

corollary prog_step_hoare:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S (st, l, h, r)} prog_step (a, st') {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (a, st') (st, l, h, r)}"
proof (cases a)
  case WB thus ?thesis using prog_WB_hoare by simp
next
  case WO thus ?thesis using prog_WO_hoare by simp
next
  case L thus ?thesis using prog_L_hoare by simp
next
  case R thus ?thesis using prog_R_hoare by simp
next
  case Nop thus ?thesis using prog_Nop_hoare by simp
qed

corollary prog_step_hoare':
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S st} prog_step i {\<lambda>s. s \<rightarrow>\<^sub>S iupdate i st}"
proof -
  obtain s l h r where "st = (s, l, h, r)"          
    using prod_cases4 by blast
  moreover obtain a st' where "i = (a, st')"
    by fastforce
  ultimately show ?thesis
    using prog_step_hoare by simp
qed

subsubsection\<open>State-Index Program\<close>

text\<open>
  In order to execute the correct step for each state,
  which create a list containing all possible transitions.
  We then compute the correct index depending on the current state and head symbol,
  and using our previously constructed \texttt{list\_index\_prog} jump to the correct step program.
\<close>

text\<open>
  We now construct a program \texttt{prog\_SI}, that computes this index:
  $$prog\_SI \quad \to \quad si \; := \; 2*s + h$$
\<close>

definition prog_SI :: "com" where
  "prog_SI \<equiv> vnSI ::= Plus (Plus (V vnS) (V vnS)) (V vnH)"

text\<open>
  The proof is again rather straight-forward.
\<close>

lemma prog_SI_correct:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S st} prog_SI {\<lambda>s. s \<rightarrow>\<^sub>S st \<and> s vnSI = int (istate_to_index st)}"
  unfolding prog_SI_def by (rule Assign', auto)

subsection\<open>Single-Step Program\<close>

text\<open>
  We can now finally construct a program that, given any Turing-Machine,
  executes the next step depending on the current state.
  Although we have built a good foundation, the core proof will still rather large.
\<close>

text\<open>
  First, we construct a list of IMP-programs from a Turing-Machine.
  The list contains all the correct instructions, mapped to their corresponding index.
  Since $s = 0$ is the final state, all following steps are $Nop$ instructions.
  Therefore, we append the list with two $Nop$ instructions, so that we can still
  use the simple $i = 2*s + h$ formula to get the index.
\<close>

definition tm_to_step_progs :: "tprog0 \<Rightarrow> com list" where
  "tm_to_step_progs tm = (
    let n = (Nop, 0) in
    map prog_step (n#n#tm)
  )"

text\<open>
  Proving this table to be correct is easy.
\<close>

lemma tm_to_step_progs_hoare:
  assumes "i < length (tm_to_step_progs tm)"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S st} (tm_to_step_progs tm)!i {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (tm @\<^sub>I i) st}"
proof -
  have "(tm_to_step_progs tm)!i = prog_step (tm @\<^sub>I i)"
    using assms tm_to_step_progs_def
    by (auto, use numeral_2_eq_2 in argo, simp add: nth_Cons')
  with prog_step_hoare' show ?thesis by simp
qed

text\<open>
  For the final \texttt{tm\_imp\_step} program, we chain the computation of the instruction-index
  together with a \texttt{list\_index\_prog}, with a table of instructions and the computed index.
\<close>

definition tm_imp_step :: "tprog0 \<Rightarrow> com" where
  "tm_imp_step p = (
    prog_SI ;;
    list_index_prog vnSI (tm_to_step_progs p) (prog_step (Nop, 0))
  )"

text\<open>
  While arguing that, given the current facts, our \texttt{tm\_imp\_step} behaves as expected might seem obvious,
  formally verifying this is not as trivial.
\<close>

lemma tm_imp_step_correct_aux:
  "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>S st} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>S istep tm st}"
  unfolding tm_imp_step_def
proof (rule Seq[where P\<^sub>2="\<lambda>s. (s \<rightarrow>\<^sub>S st) \<and> s vnSI = int (istate_to_index st)"])
  show "\<turnstile>\<^sub>t
    {\<lambda>s. s \<rightarrow>\<^sub>S st}
    prog_SI
    {\<lambda>s. (s \<rightarrow>\<^sub>S st) \<and> s vnSI = int (istate_to_index st)}"
    using prog_SI_correct by blast
next
  let ?i = "istate_to_index st"
  let ?ps = "tm_to_step_progs tm"
  show "\<turnstile>\<^sub>t
    {\<lambda>s. (s \<rightarrow>\<^sub>S st) \<and> s vnSI = int (istate_to_index st)}
    list_index_prog vnSI ?ps (prog_step (Nop, 0))
    {\<lambda>s. s \<rightarrow>\<^sub>S istep tm st}"
  proof (cases "?i < length ?ps")
    \<comment>\<open>Index is in-bounds, execute the corresponding instruction.\<close>
    case True
    then have "\<turnstile>\<^sub>t
      {\<lambda>s. s \<rightarrow>\<^sub>S st}
      ?ps!?i
      {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (tm @\<^sub>I ?i) st}"
      using tm_to_step_progs_hoare by blast
    with True have "\<turnstile>\<^sub>t     
      {\<lambda>s. s \<rightarrow>\<^sub>S st \<and> s vnSI = int (istate_to_index st)}
      list_index_prog vnSI ?ps (prog_step (Nop, 0))
      {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (tm @\<^sub>I ?i) st}"
      using list_index_prog_correct[where ps="?ps" and i="?i"
          and P="\<lambda>s. s \<rightarrow>\<^sub>S st"
          and Q="\<lambda>s. s \<rightarrow>\<^sub>S iupdate (tm @\<^sub>I ?i) st"]
      by simp
    moreover have "iupdate (tm @\<^sub>I ?i) st = istep tm st"
      using True istep_index_correct' tm_to_step_progs_def by simp
    ultimately show ?thesis by simp
  next
    \<comment>\<open>Index is out-of-bounds, execute NOP-instruction instead.\<close>
    case False
    have "\<turnstile>\<^sub>t
      {\<lambda>s. s \<rightarrow>\<^sub>S st}
      prog_step (Nop, 0)
      {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (Nop, 0) st}"
      using prog_step_hoare' by blast
    with False have "\<turnstile>\<^sub>t     
      {\<lambda>s. s \<rightarrow>\<^sub>S st \<and> s vnSI = int (istate_to_index st)}
      list_index_prog vnSI ?ps (prog_step (Nop, 0))
      {\<lambda>s. s \<rightarrow>\<^sub>S iupdate (Nop, 0) st}"
      using list_index_prog_skip[where ps="?ps" and i="?i"
          and P="\<lambda>s. s \<rightarrow>\<^sub>S st"
          and Q="\<lambda>s. s \<rightarrow>\<^sub>S iupdate (Nop, 0) st"]
      by simp
    moreover have "iupdate (Nop, 0) st = istep tm st"
      using False istep_index_skip' tm_to_step_progs_def by simp
    ultimately show ?thesis by simp
  qed
qed

lemma tm_imp_step_correct:
  assumes "(s1, l1, r1) \<Turnstile>\<langle>tm\<rangle>\<Midarrow> (s2, l2, r2)"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C (s1, l1, r1)} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C (s2, l2, r2)}"
proof -
  let ?st1 = "config_to_istate (s1, l1, r1)"
  have a1: "\<forall>s. (s \<rightarrow>\<^sub>C (s1, l1, r1)) \<longrightarrow> (s \<rightarrow>\<^sub>S ?st1)"
    using config_eq_implies_istate_eq by blast

  let ?st2 = "config_to_istate (s2, l2, r2)"
  have "istep tm ?st1 = ?st2"
    using assms istep_correct by blast
  then have a2: "\<forall>s. (s \<rightarrow>\<^sub>S istep tm ?st1) \<longrightarrow> (s \<rightarrow>\<^sub>C (s2, l2, r2))"
    using istate_eq_implies_config_eq[where c="(s2, l2, r2)"] by presburger

  from a1 a2 show ?thesis
    \<comment>\<open>We have to define the variables for conseq manually here, otherwise we get a timeout.\<close>
    using tm_imp_step_correct_aux conseq[where c="tm_imp_step tm"
        and P'="\<lambda>s. s \<rightarrow>\<^sub>C (s1, l1, r1)"
        and P="\<lambda>s. s \<rightarrow>\<^sub>S ?st1"
        and Q="\<lambda>s. s \<rightarrow>\<^sub>S istep tm ?st1"
        and Q'="\<lambda>s. s \<rightarrow>\<^sub>C (s2, l2, r2)"]
    by presburger
qed

lemma tm_imp_step_correct':
  assumes "c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c2"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c1} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C c2}"
proof -
  obtain s1 l1 r1 where c1_def: "c1 = (s1, l1, r1)"
    using prod_cases3[of c1 thesis] by simp
  obtain s2 l2 r2 where c2_def: "c2 = (s2, l2, r2)"
    using prod_cases3[of c2 thesis] by simp
  from assms c1_def c2_def show ?thesis
    using tm_imp_step_correct by simp
qed

subsection\<open>Repeated-Step Program\<close>

text\<open>
  After constructing a single-step program, we now want to construct and verify a program,
  that continuously executes steps until it reaches a final state.
\<close>

text\<open>
  Note, that since we are using a Hoare logic for total correctness, verifying it means
  also proving its termination.
  This will make proofs later a bit tricky, since:
  \begin{enumerate}
    \item Termination of Turing-Machines is inherently undecidable,
      and thus will also be undecidable for our constructed program on arbitrary inputs.
    \item Proof of Termination involve having a measurable number, that consistently
      decreases with each iteration.
      However, our state offers no such number at first glance.
  \end{enumerate}
\<close>

text\<open>
  We will solve this problem, by assuming that the TM-machine will also terminate.
  If it wouldn't, we can't pose any meaningful statements of our program, since it also wouldn't terminate.
  Given the assumed termination, we can then construct a number of steps required until a final state is reached.
  We will then use this number as our measurement of termination.
\<close>

\<comment>\<open>Continuously execute steps, until the final state (s = 0) is reached.\<close>
definition tm_imp_steps :: "tprog0 \<Rightarrow> com" where
  "tm_imp_steps p = WHILE (neq (N 0) (V vnS)) DO tm_imp_step p"

text\<open>
  This lemma will help us determine a measurable number $n$,
  that specifies the remaining amount of steps required until a final state is reached,
  under the assumption that at \textit{some point} a final state is reached.
\<close>

lemma tm_remaining_steps:
  assumes "is_final c2" and "c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c2"
  obtains n where "steps0 c1 tm n = c2"
  using assms tm_steps0_rel_iff_steps0 by blast

\<comment>\<open>If we are in a final state, executing a step yields the same configuration.\<close>
lemma step0_final:
  assumes "is_final c"
  shows "step0 c tm = c"
  using assms is_final.elims(2) by fastforce

\<comment>\<open>Same as above, but for multiple steps.\<close>
lemma steps0_final:
  assumes "is_final c"
  shows "steps0 c tm n = c"
  by (induction n) (use assms step0_final in simp)+

text\<open>
  Turing-Machines are deterministic in our model,
  which means whenver a TM reaches a final state from the same starting point,
  its final configuration will be determined:
\<close>

lemma tm_final_determined:
  assumes "c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c1" and "c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c2" and "is_final c1" and "is_final c2"
  shows "c1 = c2"
proof -
  obtain n1 where n1_def: "steps0 c tm n1 = c1"
    using assms(1) tm_steps0_rel_iff_steps0 by blast
  obtain n2 where n2_def: "steps0 c tm n2 = c2"
    using assms(2) tm_steps0_rel_iff_steps0 by blast

  consider (eq) "n1 = n2" | (n1_first) "n1 < n2" | (n2_first) "n1 > n2"
    using n1_def n2_def by linarith
  then show ?thesis proof (cases)
    case eq
    then show ?thesis
      using n1_def n2_def by simp
  next
    case n1_first
    then have "steps0 (steps0 c tm n1) tm (n2-n1) = c2"
      by (metis le_add_diff_inverse n2_def order_less_imp_le steps_add)
    then have "steps0 c1 tm (n2-n1) = c2"
      using n1_def by blast
    then show ?thesis
      using assms steps0_final by simp
  next
    case n2_first
    then have "steps0 (steps0 c tm n2) tm (n1-n2) = c1"
      by (metis le_add_diff_inverse n1_def order_less_imp_le steps_add)
    then have "steps0 c2 tm (n1-n2) = c1"
      using n2_def by blast
    then show ?thesis
      using assms steps0_final by simp
  qed
qed

subsubsection\<open>Partial Correctness\<close>

lemma total_implies_partial:
  assumes "\<turnstile>\<^sub>t {P} c {Q}"
  shows "\<turnstile> {P} c {Q}"
proof -
  have "\<Turnstile>\<^sub>t {P} c {Q}"
    using hoaret_sound assms by simp
  then have "\<Turnstile> {P} c {Q}"
    unfolding hoare_valid_def hoare_tvalid_def
    using big_step_determ by blast
  then show ?thesis
    using hoare_complete by simp
qed

lemma tm_imp_step_chain_total: "\<turnstile>\<^sub>t
  {\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')}
  tm_imp_step tm
  {\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')}"
proof -
  let ?P = "\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')"
  have "\<And>s. ?P s \<Longrightarrow> (\<exists>t. (tm_imp_step tm, s) \<Rightarrow> t \<and> ?P t)"
  proof -
    fix s :: impstate
    assume "?P s"
    then obtain c1 where c1_def: "(s \<rightarrow>\<^sub>C c1) \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c1)"
      by blast
    then obtain c2 where c2_def: "(c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c2)"
      by (simp add: tm_step0_rel_def)
    with c1_def have c2_chain: "(c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c2)"
      using tm_steps0_rel_def by force

    have "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c1} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C c2}"
      using tm_imp_step_correct' c2_def by blast
    then have "\<Turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c1} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C c2}"
      using hoaret_sound by blast
    then have "s \<rightarrow>\<^sub>C c1 \<Longrightarrow> \<exists>t. (tm_imp_step tm, s) \<Rightarrow> t \<and> (t \<rightarrow>\<^sub>C c2)"
      unfolding hoare_tvalid_def by blast
    then have "\<exists>t. (tm_imp_step tm, s) \<Rightarrow> t \<and> (t \<rightarrow>\<^sub>C c2)"
      using c1_def by blast
    then show "\<exists>t. (tm_imp_step tm, s) \<Rightarrow> t \<and> ?P t"
      using c2_chain by blast
  qed
  then show ?thesis
    using hoaret_complete hoare_tvalid_def by presburger
qed

lemma tm_imp_steps_correct_partial: "\<turnstile>
  {\<lambda>s. s \<rightarrow>\<^sub>C c}
  tm_imp_steps tm
  {\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> is_final c'}"
proof -
  let ?b = "neq (N 0) (V vnS)"
  let ?P = "\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')"

  have "\<turnstile>
    {\<lambda>s. ?P s \<and> bval ?b s}
    tm_imp_step tm
    {?P}"
  proof -
    \<comment>\<open>Downgrade from Total Correctness to Partial Correctness.\<close>
    have step: "\<turnstile> {?P} tm_imp_step tm {?P}"
      using tm_imp_step_chain_total total_implies_partial by blast
    show ?thesis by (rule partial_conseq') (use step in blast)+
  qed

  then have loop: "\<turnstile> {?P} tm_imp_steps tm {\<lambda>s. ?P s \<and> \<not> bval ?b s}"
    unfolding tm_imp_steps_def by (rule hoare.While)

  have p: "\<And>s. (s \<rightarrow>\<^sub>C c) \<Longrightarrow> (?P s)"
    using tm_steps0_rel_def by blast

  have q: "\<And>s. (?P s \<and> \<not> bval ?b s) \<Longrightarrow> (\<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> is_final c')"
  proof -
    fix s :: impstate
    assume assm: "?P s \<and> \<not> bval ?b s"
    obtain c' where c'_def: "(s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')"
      using assm by blast
    then obtain s' l' r' where c'_split: "c' = (s', l', r')"
      using prod_cases3 by blast
    moreover have "s vnS = 0"
      using assm by simp
    ultimately have "s' = 0"
      using assm c'_def by simp
    then have "is_final c'"
      using c'_def c'_split by simp
    with c'_def have "(s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> is_final c'"
      by simp
    then show "\<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> is_final c'"
      by (rule exI)
  qed

  show ?thesis by (rule partial_conseq') (use loop p q in blast)+
qed

subsubsection\<open>Total Correctness\<close>

text\<open>
  This lemma about \texttt{tm\_imp\_step} effectively says the same
  as our previous proof of correctness for it above.
  However, re-formulating the pre- and post-conditions makes it easier to integrate
  it into our proof of the WHILE-loop.
  To proof this variation of \texttt{tm\_imp\_step}, we choose a Big-Step approach.
\<close>

lemma tm_imp_step_chain':
  assumes "is_final cf"
  shows "\<Turnstile>\<^sub>t
    {\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> \<not> is_final c \<and> steps0 c tm n =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)}
    tm_imp_step tm
    {\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> n > 0 \<and> steps0 c tm (n-1) =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)}"
unfolding hoare_tvalid_def proof (standard, standard)
  fix s :: impstate
  let ?P = "\<lambda>c. s \<rightarrow>\<^sub>C c
    \<and> \<not> is_final c
    \<and> steps0 c tm n =\<^sub>C cf
    \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)"
  let ?Q = "\<lambda>t c. t \<rightarrow>\<^sub>C c \<and> n > 0 \<and> steps0 c tm (n-1) =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)"

  assume "\<exists>c. ?P c"
  then obtain c where c_def: "?P c"
    by blast

  then obtain c' where c'_def: "c' = step0 c tm"
    by simp
  then have "c \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c'"
    by (simp add: tm_step0_rel_def)
  then have "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C c'}"
    using tm_imp_step_correct' by blast
  then have "\<Turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c} tm_imp_step tm {\<lambda>s. s \<rightarrow>\<^sub>C c'}"
    using hoaret_sound by blast
  then have "\<forall>s. s \<rightarrow>\<^sub>C c \<longrightarrow> (\<exists>t. (tm_imp_step tm,s) \<Rightarrow> t \<and> t \<rightarrow>\<^sub>C c')"
    using hoare_tvalid_def by simp
  moreover have "s \<rightarrow>\<^sub>C c"
    using c_def by blast
  ultimately obtain t where t_def: "(tm_imp_step tm, s) \<Rightarrow> t \<and> (t \<rightarrow>\<^sub>C c')"
    using hoare_tvalid_def by presburger

  have a1: "(cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c')"
    using \<open>c \<Turnstile>\<langle>tm\<rangle>\<Midarrow> c'\<close> c_def tm_steps0_rel_def by force

  have a2: "n > 0" proof (cases "n = 0")
    case True
    then have "steps0 c tm n = c"
      by simp
    then have "steps0 c tm n =\<^sub>C c"
      using config_eq_refl' by simp
    moreover have "steps0 c tm n =\<^sub>C cf"
      using c_def by blast
    ultimately have "c =\<^sub>C cf"
      using config_eq_trans' config_eq_sym' by blast
    moreover have "\<not> is_final c \<and> is_final cf"
      using c_def assms by blast
    ultimately have "False"
      using config_eq_det_is_final' by simp
    then show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed

  obtain cf' where cf'_def: "steps0 c tm n = cf' \<and> cf' =\<^sub>C cf"
    using c_def by blast
  then have "steps0 c' tm (n-1) = cf'"
    using a2 c'_def by (metis Suc_diff_1 steps.simps(2))
  with cf'_def have a3: "steps0 c' tm (n-1) =\<^sub>C cf"
    by simp

  have "(tm_imp_step tm, s) \<Rightarrow> t \<and> ?Q t c'"
    using t_def c'_def a1 a2 a3 by blast
  then show "\<exists>t. (tm_imp_step tm, s) \<Rightarrow> t \<and> (\<exists>c. ?Q t c)"
    by blast
qed

lemma tm_imp_step_chain:
  assumes "is_final cf"
  shows "\<turnstile>\<^sub>t
    {\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> \<not> is_final c \<and> steps0 c tm n =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)}
    tm_imp_step tm
    {\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> n > 0 \<and> steps0 c tm (n-1) =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)}"
  using assms hoaret_complete tm_imp_step_chain' by blast

text\<open>
  Finally, we show that our \texttt{tm\_imp\_steps} program works as expected.
\<close>

lemma tm_imp_steps_correct_total:
  assumes "is_final cf" and "cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* cf"
  shows "\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C cs} tm_imp_steps tm {\<lambda>s. s \<rightarrow>\<^sub>C cf}"
proof -
  let ?b = "neq (N 0) (V vnS)"
  let ?P = "\<lambda>s. \<exists>c'. (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> s \<rightarrow>\<^sub>C c'"
  let ?T = "\<lambda>s n. \<exists>c'. s \<rightarrow>\<^sub>C c' \<and> steps0 c' tm n =\<^sub>C cf"

  have step: "\<And>n. \<turnstile>\<^sub>t
    {\<lambda>s. ?P s \<and> bval ?b s \<and> ?T s n}
    tm_imp_step tm
    {\<lambda>s. ?P s \<and> (\<exists>n'<n. ?T s n')}"
  proof -
    fix n :: nat

    let ?P' = "\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> \<not> is_final c \<and> steps0 c tm n =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)"
    let ?Q' = "\<lambda>s. \<exists>c. s \<rightarrow>\<^sub>C c \<and> n > 0 \<and> steps0 c tm (n-1) =\<^sub>C cf \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)"

    have p: "\<And>s. (?P s \<and> bval ?b s \<and> ?T s n) \<Longrightarrow> (?P' s)"
    proof -
      fix s :: impstate
      assume assm: "?P s \<and> bval ?b s \<and> ?T s n"

      obtain c where a1: "s \<rightarrow>\<^sub>C c \<and> (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c)"
        using assm by blast
      with assm have "\<exists>c'. c =\<^sub>C c' \<and> steps0 c' tm n =\<^sub>C cf"
        using impstate_to_config_inv_det' by blast
      then obtain c' where "c =\<^sub>C c' \<and> steps0 c' tm n =\<^sub>C cf"
        by blast
      then have a2: "steps0 c tm n =\<^sub>C cf"
        using config_eq_trans' config_eq_steps0 by blast

      have "s vnS \<noteq> 0"
        using assm by force
      moreover obtain st l r where "c = (st, l, r)"
        using prod_cases3 by blast
      ultimately have a3: "\<not> is_final c"
        using a1 by force

      from a1 a2 a3 show "?P' s" by blast
    qed

    have q: "\<And>s. (?Q' s) \<Longrightarrow> ?P s \<and> (\<exists>n'<n. ?T s n')"
    proof -
      fix s :: impstate
      assume assm: "?Q' s"

      have a1: "?P s"
        using assm by blast

      have "n > 0 \<and> ?T s (n-1)"
        using assm by blast
      then have a2: "\<exists>n'<n. ?T s n'"
        by (cases n, simp, auto)

      from a1 a2 show "?P s \<and> (\<exists>n'<n. ?T s n')" by blast
    qed

    show "\<turnstile>\<^sub>t
      {\<lambda>s. ?P s \<and> bval ?b s \<and> ?T s n}
      tm_imp_step tm
      {\<lambda>s. ?P s \<and> (\<exists>n'<n. ?T s n')}"
      by (rule conseq', use tm_imp_step_chain[where n=n] assms(1) in fast; use p q in blast)
  qed

  have loop: "\<turnstile>\<^sub>t
    {\<lambda>s. ?P s \<and> (\<exists>n. ?T s n)}
    tm_imp_steps tm
    {\<lambda>s. ?P s \<and> \<not> bval ?b s}"
    unfolding tm_imp_steps_def
    by (rule While, use step in simp)

  have p: "\<And>s. (s \<rightarrow>\<^sub>C cs) \<Longrightarrow> (?P s \<and> (\<exists>n. ?T s n))"
  proof -
    fix s :: impstate
    assume assm: "s \<rightarrow>\<^sub>C cs"

    have "(cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* cs) \<and> s \<rightarrow>\<^sub>C cs"
      using assm by (simp add: tm_steps0_rel_def)
    then have a1: "\<exists>c'. (cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> s \<rightarrow>\<^sub>C c'"
      by blast

    obtain n where "steps0 cs tm n =\<^sub>C cf"
      using assms tm_remaining_steps config_eq_refl' by blast
    then have a2: "(\<exists>n. ?T s n)"
      using assm by blast

    from a1 a2 show "?P s \<and> (\<exists>n. ?T s n)" by blast
  qed

  have q: "\<And>s. (?P s \<and> \<not> bval ?b s) \<Longrightarrow> (s \<rightarrow>\<^sub>C cf)"
  proof -
    fix s :: impstate
    assume assm: "?P s \<and> \<not> bval ?b s"

    obtain c where c_def: "(cs \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c) \<and> s \<rightarrow>\<^sub>C c"
      using assm by blast
    then obtain st l r where "c = (st, l, r)"
      using prod_cases3 by blast
    with assm have "is_final c"
      using c_def by simp
    with c_def show "s \<rightarrow>\<^sub>C cf"
      using assms tm_final_determined by blast
  qed

  show ?thesis by (rule conseq', use loop in fast; use p q in fast)
qed

subsection\<open>IMP is Turing-Complete\<close>

text\<open>
  We can now prove the main theorem of this project: that IMP is Turing-Complete.
  In words, we show that for every possible Turing-Machine $tm$,
  there exists an IMP-program $p$, that fulfils the following two properties:
  \begin{enumerate}
    \item For every configuration $c$, if $p$ is started in a state that represents $c$,
      when $p$ terminates it does so in state that represents a configuration $c'$,
      where $tm$ will also reach $c'$ if started in $c$ and which is a final-configuration,
      meaning the $tm$ would also halt in exactly this configuration.
    \item For every two configurations $c_1$ and $c_2$, where $c_2$ is a final-configuration,
      and $tm$ would also reach (and halt) in $c_2$ if started in $c_1$, then our program,
      if started in a state that represents $c_1$, will terminate and its final state
      will represent $c_2$.
  \end{enumerate}
  This shows, that when our constructed program terminates, it does so in a state we expect.
  Furthermore, this also shows that our constructed program always terminates, when we expect it to.
\<close>

theorem IMP_is_TuringComplete:
  fixes tm :: tprog0
  obtains p where "\<And>c. \<turnstile> {\<lambda>s. s \<rightarrow>\<^sub>C c} p {\<lambda>s. \<exists>c'. (s \<rightarrow>\<^sub>C c') \<and> (c \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c') \<and> is_final c'}"
    and "\<And>c1 c1. (is_final c2 \<and> (c1 \<Turnstile>\<langle>tm\<rangle>\<Midarrow>\<^sup>* c2)) \<Longrightarrow> (\<turnstile>\<^sub>t {\<lambda>s. s \<rightarrow>\<^sub>C c1} p {\<lambda>s. s \<rightarrow>\<^sub>C c2})"
  using tm_imp_steps_correct_partial tm_imp_steps_correct_total by blast

text\<open>
  The attentive reader will have noticed, that the first statement is formulated logically
  a bit differently, than described in words above.
  Precisely, we actually only show, that there exists a configuration $c'$,
  that is represented by the state $s$, and that is final and reachable from $c$,
  but not that is uniquely defined.
\<close>

text\<open>
  This problem again stems from the ambigiuous definition of tapes in the imported definition.
  However, we have shown earlier in lemma \hyperref[lem:impstate_to_config_inv_det]{impstate\_to\_config\_inv\_det}
  that all possible configurations that could occur must be semantically equivalent
  with respect to our equivalence relation $=_C$.
\<close>

text\<open>
  With this, we have shown that IMP is Turing-Complete. $\square$
\<close>

end \<comment>\<open>end-theory IMP\_TuringComplete\<close>

section\<open>Closing Remarks\<close>

subsection\<open>Conclusion\<close>

text\<open>
  We have shown that IMP, as introduced by Tobias Nipkow and Gerwin Klein in
  ``Concrete Semantics''\<^cite>\<open>"Nipkow2014"\<close>, is Turing-Complete,
  by constructing an IMP-program, that can simulate a Turing-Machine.
\<close>

subsection\<open>Future Work\<close>

text\<open>
  A possible continuation of this project could be to show the Turing-Equivalence of IMP:
  that is, showing that IMP can also be simulated by a Turing-Machine.
  Although, the widely-accepted Church-Turing-thesis implies that IMP can not be more powerful than a Turing-Machine.
  \<^cite>\<open>"Copeland1997"\<close>
\<close>

text\<open>
  Another interesting future work could be investigating how different language features change the powerfulnes of IMP.
  For example, what effects would adding non-determinism (e.g. by an infinite loop statement) have,
  or what boundaries can be imposed without violating the Turing-Completeness.
\<close>

text\<open>
  Furthermore, this project could also be refined, replacing some abbreviations with definitions,
  making some proofs more difficult or require more facts, but also speeding up other proofs significantly.
  Some more utility lemmas can also be introduced, making some facts more directly derivable.
  Last, but not least, the Hoare pre-conditions and post-conditions may be refined in various facts,
  so that facts about them may be used more easily by other proofs.
\<close>
