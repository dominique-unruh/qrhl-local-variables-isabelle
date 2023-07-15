section \<open>Helping Lemmas\<close>

theory Helping_Lemmas
  imports Assumptions Comm_Idem_Modulo
begin

instance predicate :: bounded_lattice
  by (rule instance_predicate_lattice)

lemma idx_inj[simp]: "idx b x = idx c y \<longleftrightarrow> b = c \<and> x = y"
  apply (cases x; cases y) 
  using idxq_inj idxc_inj by auto

lemma idx_inj'[simp]: "inj (idx c)"
  apply (rule injI) by simp

lemma idx12_union: "idx12 (X \<union> Y) = idx12 X \<union> idx12 Y"
  unfolding idx12_def by auto
lemma idx12_inter: "idx12 (X \<inter> Y) = idx12 X \<inter> idx12 Y"
  unfolding idx12_def by auto
lemma idx12_diff: "idx12 (X - Y) = idx12 X - idx12 Y"
  unfolding idx12_def by auto
lemma idx12_empty[simp]: "idx12 {} = {}"
  unfolding idx12_def by auto
lemma idx12_empty'[simp]: "idx12 X = {} \<longleftrightarrow> X = {}"
  unfolding idx12_def by auto
lemma idx12_insert[simp]: "idx12 (insert x X) = insert (idx True x) (insert (idx False x) (idx12 X))"
  unfolding idx12_def by auto

lemma is_classical_QVar[simp]: "\<not> is_classical (QVar q)"
  using is_classical.cases by blast
lemma is_classical_idx[simp]: "is_classical (idx b x) = is_classical x"
  apply (cases x; cases b)
  using is_classical.cases is_classical.intros by auto

lemma fve_some_constant[simp]: "fve some_constant = {}"
  unfolding some_constant_def apply (rule someI_ex) by (rule ex_constant)

lemma substitute_program:
  assumes "program p"
  shows "substitute p s = p"
  using assms apply induction by auto

lemma program_substitute[intro]:
  assumes "\<And>i. program (s i)"
  shows "program (substitute C s)"
  apply (induction C)
  by (auto intro!: assms program.intros)


lemma finite_fv[simp]: "finite (fv C)"
  apply (induction C) by auto

lemma fv_subst: "fv (substitute C s) \<supseteq> fv C"
  apply (induction C) by auto

lemma fv_subst': "fv (substitute C s) \<subseteq> fv C \<union> ((\<Union>i\<in>holes C. fv (s i)) - covered C)"
  apply (induction C) by auto

lemma program_inner: 
  assumes "program p"
  shows "inner p = {}"
  using assms apply induction by auto

lemma program_covered: 
  assumes "program p"
  shows "covered p = UNIV"
  using assms apply (induction p) by auto

lemma fv_subst_covered: "fv (substitute C s) \<inter> covered C = fv C \<inter> covered C"
  apply (induction C) by auto

lemma covered_subst: "covered (substitute C s) \<supseteq> covered C \<union> (\<Inter>i\<in>holes C. covered (s i))"
  apply (induction C) by auto

lemma finite_overwr[simp]: "finite (overwr C)"
  apply (induction C) by auto

lemma overwr_fv: "overwr C \<subseteq> fv C"
  apply (induction C) by auto


lemma overwr_subst: "overwr (substitute C s) \<supseteq> overwr C"
proof (induction C)
  case (Seq C1 C2)
  then show ?case 
    using covered_subst fv_subst_covered by fastforce+
qed auto


lemma finite_written[simp]: "finite (written C)"
  apply (induction C) by auto

lemma "quantum' (fv C) \<subseteq> written C"
  apply (induction C) by (auto simp: quantum'_def)

lemma denot_eq'_refl[simp]: "C =d= C"
  by (simp add: denot_eq'_def program.intros(3) program_substitute)

lemma denot_eq'_reflI[simp]: "C = D \<Longrightarrow> C =d= D"
  by simp

lemma denot_eq'_sym: "C =d= D \<Longrightarrow> D =d= C"
  by (simp add: denot_eq'_def denot_eq_sym program.intros(3) program_substitute)

lemma denot_eq'_cong_local: "C =d= D \<Longrightarrow> Local X C =d= Local X D"
  by (simp add: denot_eq'_def denot_eq_cong_local program.intros(3) program_substitute)

lemma denot_eq'_trans[trans]: "C =d= D \<Longrightarrow> D =d= E \<Longrightarrow> C =d= E"
  by (metis (no_types, lifting) denot_eq'_def denot_eq_trans program.intros(3) program_substitute)

lemma equivp_denot_eq'[simp]: "equivp (=d=)"
  apply (auto intro!: equivpI reflpI sympI transpI)
  using denot_eq'_sym apply blast
  using denot_eq'_trans by blast

lemma written_subst_Skip[simp]: "written (substitute c (\<lambda>_. Skip)) = written c"
  apply (induction c) by auto
lemma fv_subst_Skip[simp]: "fv (substitute c (\<lambda>_. Skip)) = fv c"
  apply (induction c) by auto
lemma overwr_subst_Skip: "overwr p \<subseteq> overwr (substitute p (\<lambda>_. Skip))"
  apply (induction p) apply (simp_all)
    apply blast
   apply blast
  using program.intros(3) program_covered program_substitute by auto

lemma written_subst': "written (substitute C s)
  \<subseteq> written C \<union> (\<Union>i\<in>holes C. written (s i))"
  apply (induction C) by auto

lemma inner_subst': "inner (substitute C s)
  \<subseteq> inner C \<union> (\<Union>i\<in>holes C. inner (s i))"
proof (induction C)
  case (Local v C)
  show ?case
  proof (cases "program (substitute C s)")
    case True
    then show ?thesis
      by simp
  next
    case False
    with Local show ?thesis
      apply auto
      apply (metis inner.simps(12) insert_iff substitute_program)
      by (metis (no_types, lifting) UN_iff Un_iff inner.simps(12) insertCI subsetD substitute_program)
  qed
qed auto

lemma seq:
  assumes "qRHL A p1 p2 B"
  assumes "qRHL B p1' p2' C"
  shows "qRHL A (p1; p1') (p2; p2') C"
  using assms(1) assms(2) program.intros(3) program_substitute qRHL_def seq0 by auto

lemma conseq_post:
  assumes "qRHL A p1 p2 B"
  assumes "B \<le> C"
  shows "qRHL A p1 p2 C"
  using assms(1) assms(2) conseq_post0 program.intros(3) program_substitute qRHL_def by auto


lemma denot_eq_seq_assoc:
  shows "(c; d); e =d= c; (d; e)"
  by (simp add: denot_eq'_def denot_eq_seq_assoc0 program.intros(3) program_substitute)

lemma denot_eq_seq_cong1:
  assumes "c =d= d"
  shows "c; e =d= d; e"
  using assms denot_eq'_def denot_eq_seq_cong10 program.intros(3) program_substitute by auto

lemma denot_eq_seq_cong2:
  assumes "c =d= d"
  shows "e; c =d= e; d"
  using assms denot_eq'_def denot_eq_seq_cong20 program.intros(3) program_substitute by auto

lemma denot_eq_while_cong:
  assumes "c =d= d"
  shows "While e c =d= While e d"
  using assms denot_eq'_def denot_eq_while_cong0 program.intros program_substitute by auto

lemma denot_eq_ifte_cong1:
  assumes "c =d= d"
  shows "IfTE f c e =d= IfTE f d e"
  using assms denot_eq'_def denot_eq_ifte_cong10 program.intros program_substitute by auto

lemma denot_eq_ifte_cong2:
  assumes "c =d= d"
  shows "IfTE f e c =d= IfTE f e d"
  using assms denot_eq'_def denot_eq_ifte_cong20 program.intros program_substitute by auto

lemma denot_eq_qrhl_left:
  assumes "p1 =d= p1'"
  shows "qRHL A p1 p2 B \<longleftrightarrow> qRHL A p1' p2 B"
  using assms denot_eq'_def denot_eq_qrhl_left0 program.intros(3) program_substitute qRHL_def by auto

lemma denot_eq_qrhl_right:
  assumes "p2 =d= p2'"
  shows "qRHL A p1 p2 B \<longleftrightarrow> qRHL A p1 p2' B"
  using assms denot_eq'_def denot_eq_qrhl_right0 program.intros(3) program_substitute qRHL_def by auto

lemma denot_eq_init:
  assumes "CVar ` set X \<subseteq> overwr p"
  shows "Assign X some_constant; p =d= p"
  by (smt assms denot_eq'_def denot_eq_init0 overwr_subst program.intros(3) program_substitute subset_trans substitute.simps(3) substitute.simps(7))

lemma denot_eq_qinit:
  assumes "distinct Q"
  assumes "QVar ` set Q \<subseteq> overwr p"
  shows "QInit Q some_constant; p =d= p"
  by (smt assms(1) assms(2) denot_eq'_def denot_eq_qinit0 overwr_subst program.intros(3) program.intros(4) program_substitute subset_trans substitute.simps(3) substitute_program)


lemma assign_Eq: "qRHL top (Assign X some_constant) (Assign X some_constant) (Eq0 (CVar ` set X))"
  by (simp add: assign_Eq0 qRHL_def)

lemma qinit_Eq: "distinct Q \<Longrightarrow> qRHL top (QInit Q some_constant) (QInit Q some_constant) (Eq0 (QVar ` set Q))"
  by (simp add: qRHL_def qinit_Eq0)

lemma frame_rule:
  fixes c d R
  assumes "(idx True ` written c) \<inter> fvp R = {}"
  assumes "(idx False ` written d) \<inter> fvp R = {}"
  assumes "qRHL A c d B"
  shows "qRHL (A \<sqinter> R) c d (B \<sqinter> R)"
  using assms frame_rule0 program.intros(3) program_substitute qRHL_def by auto

lemma varchange:
  assumes "is_quantum' Q" and "is_quantum' Q'"
  assumes "q \<in> Q" and "infinite_var q"
  assumes "(fvp A \<union> fvp B) \<inter> (idx12 Q \<inter> idx12 Q') = {}"
  assumes "(fv c \<union> fv d) \<inter> (Q \<union> Q') = {}"
  assumes "qRHL (A \<sqinter> Eq0 (Vl \<union> Q)) c d (B \<sqinter> Eq0 (Vr \<union> Q))"
  shows "qRHL (A \<sqinter> Eq0 (Vl \<union> Q')) c d (B \<sqinter> Eq0 (Vr \<union> Q'))"
  unfolding qRHL_def
  apply (rule varchange0)
  using assms unfolding qRHL_def
  by (auto intro!: program_substitute program.intros)

lemma drop_Eq:
  assumes "is_classical' X"
  assumes "fvp A \<inter> idx12 X = {}"
  assumes "fv c \<inter> X = {}"
  assumes "fv d \<inter> X = {}"
  assumes "qRHL (A \<sqinter> Eq0 X) c d B"
  shows "qRHL A c d B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) drop_Eq0 program.intros(3) program_substitute qRHL_def by auto

lemma equal_rule:
  assumes "fv p \<subseteq> V"
  shows "qRHL (Eq0 V) p p (Eq0 V)"
  by (simp add: assms equal_rule0 program.intros(3) program_substitute qRHL_def)

lemma joint_while_rule:
  assumes "A \<le> Eq0 (CVar ` fve e)"
  assumes "qRHL A c d A"
  shows "qRHL A (While e c) (While e d) A"
  using assms(1) assms(2) joint_while_rule0 program.intros(3) program_substitute qRHL_def by auto

lemma joint_if_rule:
  assumes "A \<le> Eq0 (CVar ` fve e)"
  assumes "qRHL A c1 c2 B"
  assumes "qRHL A d1 d2 B"
  shows "qRHL A (IfTE e c1 d1) (IfTE e c2 d2) A"
  using assms(1) assms(2) assms(3) joint_if_rule0 program.intros(3) program_substitute qRHL_def by auto

lemma joint_local0_rule:
  fixes U1 U2 W1 W2
  defines \<open>Eq' \<equiv> Eq (U1,U2,W1,W2)\<close>
  assumes "idx True v \<notin> fvp A"
  assumes "idx False v \<notin> fvp A"
  assumes "v \<notin> S"
  assumes "v \<notin> R"
  assumes \<open>insert v S \<inter> QVar ` (set W1 \<union> set W2) = {}\<close>
  assumes "qRHL (A \<sqinter> Eq' (insert v S)) c d (A \<sqinter> Eq' (insert v R))"
  shows "qRHL (A \<sqinter> Eq' S) (Local v c) (Local v d) (A \<sqinter> Eq' R)"
  using assms joint_local0_rule0 program.intros(3) program_substitute qRHL_def by auto

lemma joint_init_eq0:
  assumes "QVar ` set Q \<subseteq> V"
  assumes "is_quantum' V"
  shows "qRHL (Eq0 V) 
        (QInit Q some_constant) (QInit Q some_constant)
        (Eq0 (V - QVar ` set Q))"
  
  by (simp add: assms(1) assms(2) joint_init_eq00 qRHL_def)

lemma seq_c_skip[simp]: "c; Skip =d= c"
  by (simp add: denot_eq'_def program.intros(3) program_substitute)

lemma seq_skip_c[simp]: "Skip; c =d= c"  
  by (simp add: denot_eq'_def program.intros(3) program_substitute)

lemma local_idem[simp]: "Local x (Local x C) =d= Local x C"
  by (simp add: denot_eq'_def program.intros(3) program_substitute) 

lemma local_swap: "Local x (Local y C) =d= Local y (Local x C)"
  by (simp add: denot_eq'_def local_swap0 program.intros(3) program_substitute)


lemmas seq_trans[trans] = seq[rotated 2]

lemmas conseq_post_trans[trans] = conseq_post[rotated 2]

lemmas denot_eq_qrhl_left_trans[trans] = denot_eq_qrhl_left[rotated 1, THEN iffD1, rotated -1]

lemmas denot_eq_qrhl_right_trans[trans] = denot_eq_qrhl_right[rotated 1, THEN iffD1, rotated -1]

lemma fvp_inter_empty:
  assumes "X \<inter> fvp A = {}"
  assumes "X \<inter> fvp B = {}"
  shows "X \<inter> fvp (A \<sqinter> B) = {}"
  using assms fvp_inter by blast 

lemma Eq_split': 
  assumes "is_classical' Y"
  shows "Eq0 (X \<union> Y) = Eq0 X \<sqinter> Eq0 Y"
  using Eq_split assms
  by (metis Un_commute inf_commute)

lemma X_inter_CVar: "X \<inter> range CVar = classical' X"
  unfolding classical'_def apply auto
  using is_classical.cases by blast

lemma X_inter_QVar: "X \<inter> range QVar = quantum' X"
  unfolding quantum'_def apply auto
  by (metis (full_types) is_classical.intros rangeI var.exhaust)


lemma fv_block[simp]: "fv (block L) = (\<Union>c\<in>set L. fv c)"
  apply (induction L) by auto

lemma program_blockI[intro]: 
  assumes "\<And>x. x\<in>set b \<Longrightarrow> program x"
  shows "program (block b)"
  using assms apply (induction b)
  by (auto simp: program.intros)


global_interpretation locals: comm_idem_modulo Local denot_eq'
  defines locals = locals.F
  apply unfold_locales
     apply simp
    apply (simp add: denot_eq'_def denot_eq_cong_local program.intros(3) program_substitute)
   apply simp
  by (simp add: local_swap)

lemma program_localsI[intro]:
  assumes "finite V"
  assumes "program c"
  shows "program (locals V c)"
  using assms(1)
  apply (induction rule: locals.F_induct)
  using assms program.intros by auto

lemma fv_locals[simp]: 
  assumes "finite V"
  shows "fv (locals V c) = fv c - V"
  using assms apply (induction rule:locals.F_induct)
  by auto


lemma program_init[simp]:
  "program (init v)"
  by (cases v, auto simp: program.intros)

lemma init_idem: "init x; init x =d= init x"
  apply (cases x)
  by (auto intro!: denot_eq_qinit denot_eq_init)

lemma overwr_init[simp]: "overwr (init v) = {v}"
  apply (cases v) by auto
lemma fv_init[simp]: "fv (init v) = {v}"
  apply (cases v) by auto
lemma covered_init[simp]: "covered (init v) = UNIV"
  apply (cases v) by auto

lemma swap:
  assumes "fv c \<inter> fv d = {}"
  shows "c;d =d= d;c"
  by (simp add: assms denot_eq'_def program.intros(3) program_substitute swap0)



global_interpretation inits: comm_idem_modulo \<open>\<lambda>v c. Seq (init v) c\<close> "(=d=)"
proof unfold_locales
  show "equivp (=d=)"
    by simp
  fix a b x  
  show "a =d= b \<Longrightarrow>
       init x; a =d= init x; b"
    by (simp add: denot_eq_seq_cong2)
  fix z
  show "init x; (init x; z) =d= init x; z"
  proof -
    have "init x; (init x; z) =d= (init x; init x); z"
      by (simp add: denot_eq_seq_assoc locals.R_sym)
    also have "\<dots> =d= init x; z"
      by (simp add: denot_eq_seq_cong1 init_idem)
    finally show ?thesis
      by -
  qed
  fix y
  show "(init y; (init x; z)) =d=
        (init x; (init y; z))"
  proof -
    have "(init y; (init x; z)) =d= (init y; init x); z"
      by (simp add: denot_eq_seq_assoc locals.R_sym)
    also have "\<dots> =d= (init x; init y); z"
      apply (rule denot_eq_seq_cong1)
      apply (cases "x=y", simp)
      by (auto intro!: swap)
    also have "\<dots> =d= (init x; (init y; z))"
      by (simp add: denot_eq_seq_assoc locals.R_sym)
    finally show ?thesis
      by -
  qed
qed

definition "inits V = inits.F V Skip"

lemma inits_empty[simp]: "inits {} = Skip"
  unfolding inits_def by simp

lemmas locals_foldr = locals.F_foldr

lemma program_initsFI[intro]:
  assumes "finite V"
  assumes "program c"
  shows "program (inits.F V c)"
  using assms(1)
  apply (induction rule: inits.F_induct)
  using assms program.intros by auto

lemma program_initsI[intro]:
  assumes "finite V"
  shows "program (inits V)"
  using assms inits_def program.intros(3) by auto


lemmas denot_eq_cong_locals = locals.R_cong_F

lemmas locals_join = locals.F_join

lemma fv_inits[simp]: 
  assumes "finite V"
  shows "fv (inits V) = V"
  using assms unfolding inits_def
  apply (induction rule:inits.F_induct)
  by auto

lemma overwr_inits[simp]: 
  assumes "finite V"
  shows "overwr (inits V) = V"
  using assms unfolding inits_def
  apply (induction rule:inits.F_induct)
  by auto

lemma covered_inits[simp]: 
  assumes "finite V"
  shows "covered (inits V) = UNIV"
  using assms unfolding inits_def
  apply (induction rule:inits.F_induct)
  by auto

lemma overwr_locals[simp]: 
  assumes "finite V"
  shows "overwr (locals V c) = overwr c - V"
  using assms 
  apply (induction rule:locals.F_induct)
  by auto

lemma covered_locals[simp]: 
  assumes "finite V"
  shows "covered (locals V c) = covered c \<union> V"
  using assms 
  apply (induction rule:locals.F_induct)
  by auto

lemma local_unused:
  assumes "x \<notin> fv C"
  shows "Local x C =d= C"
  using assms by (auto simp: denot_eq'_def intro!: local_unused0 program_substitute program.intros)

lemma locals_unused:
  assumes "finite V"
  assumes "V \<inter> fv C = {}"
  shows "locals V C =d= C"
  using assms
  apply (induction rule:locals.F_induct)
   apply simp
  by (meson insert_disjoint(1) local_unused locals.R_trans locals.cong_R)

lemma local_seq_merge:
  shows "Local x c1; Local x c2 =d= Local x (c1; init x; c2)"
  by (auto simp: substitute_program denot_eq'_def intro!: program_substitute program.intros local_seq_merge0)

lemma local_seq2:
  assumes "x \<notin> fv c1"
  shows "c1; Local x c2 =d= Local x (c1; c2)"
proof -
  have "c1; Local x c2 =d= Local x c1; Local x c2"
    using assms denot_eq_seq_cong1 local_unused locals.R_sym by blast
  also have "\<dots> =d= Local x (c1; init x; c2)"
    by (simp add: local_seq_merge)
  also have "\<dots> =d= Local x (init x; c1; c2)"
    by (simp add: Helping_Lemmas.swap assms denot_eq_seq_cong1 locals.cong_R)
  also have "\<dots> =d= Local x (init x; (c1; c2))"
    by (simp add: comm_idem_modulo.cong_R denot_eq_seq_assoc locals.comm_idem_modulo_axioms)
  also have "\<dots> =d= Local x (c1; c2)"
    by (smt denot_eq'_def local_init_beginning0 locals.R_sym program.intros(3) program_init program_substitute substitute.simps(3) substitute.simps(6) substitute_program)
  finally show ?thesis
    by -
qed


lemma locals_seq2:
  assumes "finite V"
  assumes "V \<inter> fv c1 = {}"
  shows "c1; locals V c2 =d= locals V (c1; c2)"
  using assms
proof (induction V)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  then have [simp]: "finite F" by -

  have "c1; locals (insert x F) c2 =d= c1; Local x (locals F c2)"
    by (simp add: denot_eq_seq_cong2 locals.F_insert)
  also have "\<dots> =d= Local x (c1; (locals F c2))"
    using insert.prems local_seq2 by auto
  also have "\<dots> =d= Local x (locals F (c1; c2))"
    using denot_eq'_cong_local insert.IH insert.prems by blast
  also have "\<dots> =d= locals (insert x F) (c1 ; c2)"
    using denot_eq'_sym insert.hyps(1) locals.F_insert by blast
  finally show ?case 
    by -
qed

lemma inits_singleton[simp]: "inits {x} =d= init x"
  unfolding inits_def by auto

lemma init_inits:
  assumes "finite V"
  shows "init x; inits V =d= inits (insert x V)"
  by (simp add: assms equivp_symp inits.F_insert inits.equiv_R inits_def)

lemma inits_init:
  assumes "finite V"
  shows "inits V; init x =d= inits (insert x V)"
  using assms 
proof (induction V)
  case empty
  have "inits {} ; init x =d= init x"
    by auto
  also have "init x =d= inits {x}"
    by (simp add: locals.R_sym)
  finally show ?case 
    by -
next
  case (insert y F)
  have "inits (insert y F); init x =d= init y; inits F; init x"
    using denot_eq_seq_cong1 inits.F_insert inits_def insert.hyps(1) program.intros(10) program_initsI by auto
  also have "\<dots> =d= init y; (inits (insert x F))"
    by (meson denot_eq_seq_assoc inits.cong_R insert.IH insert.hyps(1) locals.R_trans program_init program_initsI)
  also have "\<dots> =d= inits (insert y (insert x F))"
    by (simp add: init_inits insert.hyps(1))
  finally show ?case
    by (simp add: insert_commute)
qed

lemma locals_seq_merge:
  assumes "finite V"
  assumes [simp]: "program c1" and "program c2"
  shows "locals V c1; locals V c2 =d= locals V (c1; inits V; c2)"
  using assms
proof (induction V arbitrary: c2)
  case empty
  then show ?case
    by (simp add: denot_eq_seq_cong1 locals.R_sym program.intros(10) program.intros(3)) 
next
  case (insert x F)
  then have [simp]: "program c2" and [simp]: "finite F"
    by auto
  have "locals (insert x F) c1; locals (insert x F) c2
    =d= Local x (locals F c1); locals (insert x F) c2"
    by (simp add: denot_eq_seq_cong1 locals.F_insert program.intros(9) program_localsI)
  also have "\<dots> =d= Local x (locals F c1); Local x (locals F c2)"
    by (simp add: denot_eq_seq_cong2 locals.F_insert program.intros(9) program_localsI)
  also have "\<dots> =d= Local x (locals F c1; (init x; locals F c2))"
    by (meson insert denot_eq'_cong_local denot_eq_seq_assoc insert.hyps(1) local_seq_merge locals.R_trans program_init program_localsI)
  also have "\<dots> =d= Local x (locals F c1; locals F (init x; c2))"
    by (simp add: denot_eq'_cong_local denot_eq_seq_cong2 insert.hyps(2) locals_seq2 program.intros(10) program_localsI)
  also have "\<dots> =d= Local x (locals F (c1; inits F; (init x; c2)))"
    by (simp add: denot_eq'_cong_local insert.IH program.intros(10))
  also have "\<dots> =d= Local x (locals F (c1; (inits F; init x); c2))"
    apply (auto intro!: denot_eq'_cong_local denot_eq_cong_locals)
    apply (rule denot_eq'_trans)
     apply (rule denot_eq_seq_assoc[THEN denot_eq'_sym])
    by (auto intro!: denot_eq_seq_cong1 program.intros denot_eq_seq_assoc)
  also have "\<dots> =d= Local x (locals F (c1; inits (insert x F); c2))"
    using inits_init
    by (simp add: denot_eq'_cong_local denot_eq_cong_locals denot_eq_seq_cong1 denot_eq_seq_cong2 inits_def program.intros(10) program.intros(3) program_initsFI)
  also have "\<dots> =d= locals (insert x F) (c1; inits (insert x F); c2)"
    using denot_eq'_sym insert.hyps(1) locals.F_insert by blast
  finally show ?case 
    by -
qed

lemma inits_inits:
  assumes "finite V" and "finite W"
  shows "inits V; inits W =d= inits (V\<union>W)"
  using assms(1) 
proof (induction V)
  case empty
  show ?case by simp
next
  case (insert x F)
  have "inits (insert x F); inits W =d= (init x; inits F); inits W"
    by (simp add: denot_eq_seq_cong1 inits.F_insert inits_def insert.hyps(1))
  also have "\<dots> =d= init x; inits (F \<union> W)"
    using denot_eq_seq_assoc denot_eq_seq_cong2 insert.IH locals.R_trans by blast
  also have "\<dots> =d= inits (insert x (F \<union> W))"
    by (simp add: assms(2) init_inits insert.hyps(1))
  finally show ?case
    by simp
qed

lemma local_init_end:
  shows "Local x (c; init x) =d= Local x c"
  unfolding denot_eq'_def
  by (simp add: local_init_end0 program.intros(3) program_substitute substitute_program)

lemma locals_init_end:
  assumes "finite V"
  assumes "x \<in> V"
  shows "locals V (c; init x) =d= locals V c"
  using assms
proof (induction V)
  case empty
  then show ?case by auto
next
  case (insert y F)
  show ?case
  proof (cases "x = y")
    case True
    have "locals (insert x F) (c; init x) =d=
          locals F (Local x (c; init x))"
      by (simp add: insert.hyps(1) locals.F_insert')
    also have "\<dots> =d= locals F (Local x c)"
      by (simp add: denot_eq_cong_locals local_init_end)
    also have "\<dots> =d= locals (insert x F) c"
      using denot_eq'_sym insert.hyps(1) locals.F_insert' by blast
    finally show ?thesis
      by (simp add: True)
  next
    case False
    have "locals (insert y F) (c; init x) =d= 
          Local y (locals F (c; init x))"
      by (simp add: insert.hyps(1) locals.F_insert)
    also have "\<dots> =d= Local y (locals F c)"
      apply (rule denot_eq'_cong_local)
      apply (rule insert.IH)
      using False insert by auto
    also have "\<dots> =d= locals (insert y F) c"
      using insert.hyps(1) locals.F_insert locals.R_sym by blast
    finally show ?thesis
      by -
  qed
qed

lemma locals_inits_end:
  assumes "finite V"
  assumes "W \<subseteq> V"
  shows "locals V (c; inits W) =d= locals V c"
proof -
  from assms have "finite W"
    using infinite_super by blast 
  then show ?thesis
  proof (insert \<open>W \<subseteq> V\<close>, induction W)
    case empty
    show ?case
      by (simp add: denot_eq_cong_locals)
  next
    case (insert x F)
    have "locals V (c; inits (insert x F))
      =d= locals V (c; inits F; init x)"
      by (metis denot_eq_cong_locals denot_eq_seq_assoc denot_eq_seq_cong2 equivp_def equivp_symp inits.equiv_R inits_init insert.hyps(1))
    also have "\<dots> =d= locals V (c; inits F)"
      apply (rule locals_init_end)
      using assms insert by auto
    also have "\<dots> =d= locals V c"
      using insert.IH insert.prems by blast
    finally show ?case
      by -
  qed
qed

lemma local_init_beginning:
  shows "Local x c =d= Local x (init x; c)"
  unfolding denot_eq'_def
  by (simp add: local_init_beginning0 program.intros(3) program_substitute substitute_program)

lemma locals_inits_beginning:
  assumes "finite V"
  shows "locals V c =d= locals V (inits V; c)"
  using assms
proof (induction V arbitrary: c)
  case empty
  show ?case
    by (simp add: locals.R_sym) 
next
  case (insert x V)
  have "locals (insert x V) c =d= locals V (Local x c)"
    by (simp add: insert.hyps(1) locals.F_insert')
  also have "\<dots> =d= locals V (Local x (init x; c))"
    using local_init_beginning
    by (simp add: denot_eq_cong_locals)
  also have "\<dots> =d= locals (insert x V) (init x; c)"
    using denot_eq'_sym insert.hyps(1) locals.F_insert' by blast
  also have "\<dots> =d= Local x (locals V (init x; c))"
    by (simp add: insert.hyps(1) locals.F_insert)
  also have "\<dots> =d= Local x (locals V (inits V; init x; c))"
    by (metis denot_eq_cong_locals denot_eq_seq_assoc equivp_def inits.equiv_R insert.IH locals.cong_R)
  also have "\<dots> =d= Local x (locals V (inits (insert x V); c))"
    by (simp add: denot_eq_cong_locals denot_eq_seq_cong1 inits_init insert.hyps(1) locals.cong_R)
  also have "\<dots> =d= locals (insert x V) (inits (insert x V); c)"
    using insert.hyps(1) locals.F_insert locals.R_sym by blast
  finally show ?case
    by -
qed

lemma locals_inits_change:
  assumes "finite X" and "finite V"
  assumes "(X-Y) \<union> (Y-X) \<subseteq> V"
  shows "locals V (inits X; c) =d= locals V (inits Y; c)"
proof -
  have 1: "V \<union> X = V \<union> Y \<union> X" and 2: "V \<union> Y = V \<union> Y \<union> X"
    using Diff_partition assms(3) by blast+
  have "locals V (inits X; c) =d= locals V (inits V; (inits X; c))"
    by (simp add: assms(2) locals_inits_beginning)
  also have "\<dots> =d= locals V ((inits V; inits X); c)"
    using denot_eq'_sym denot_eq_cong_locals denot_eq_seq_assoc by blast
  also have "\<dots> =d= locals V (inits (V\<union>Y\<union>X); c)"
    using 1
    by (metis assms(1) assms(2) denot_eq_cong_locals denot_eq_seq_cong1 inits_inits)
  also have "\<dots> =d= locals V ((inits V; inits Y); c)"
    using 2
    by (metis "1" assms(1) assms(2) denot_eq_cong_locals denot_eq_seq_cong1 finite_Un inits_inits locals.R_sym)
  also have "\<dots> =d= locals V (inits V; (inits Y; c))"
    using denot_eq_cong_locals denot_eq_seq_assoc by blast
  also have "\<dots> =d= locals V (inits Y; c)"
    using assms(2) locals.R_sym locals_inits_beginning by blast
  finally show ?thesis
    by -
qed

lemma init_overwr:
  assumes "x \<in> overwr c"
  shows "init x; c =d= c"
  using assms apply (cases x; simp)
   apply (rule denot_eq_qinit; simp)
  by (rule denot_eq_init; simp)

lemma inits_overwr:
  assumes "X \<subseteq> overwr c"
  shows "inits X; c =d= c"
proof -
  have "finite X"
    using assms finite_overwr infinite_super by blast
  then show ?thesis
    using assms
  proof (induction X arbitrary: c)
    case (insert x X)
    have "inits (insert x X); c =d= init x; inits X; c"
      by (simp add: denot_eq_seq_cong1 inits.F_insert inits_def insert.hyps(1))
    also have "\<dots> =d= init x; c"
      by (metis denot_eq_seq_assoc denot_eq_seq_cong2 equivp_def inits.equiv_R insert.IH insert.prems insert_subset)
    also have "\<dots> =d= c"
      using init_overwr insert.prems by blast
    finally show ?case
      by -
  qed auto
qed


lemma change_Eq_precondition:
  assumes VW_overwr: "V - W \<subseteq> overwr c \<inter> overwr d"
  assumes WV_overwr: "quantum' (W - V) \<subseteq> overwr c \<inter> overwr d"
  assumes "finite V" and "finite W"
  assumes VW_R: "idx12 (V-W) \<sqinter> fvp R = {}"
  assumes WV_R: "idx12 (quantum' (W-V)) \<sqinter> fvp R = {}"
  assumes qrhl: "qRHL (R \<sqinter> Eq0 V) c d B"
  shows "qRHL (R \<sqinter> Eq0 W) c d B"
proof -

  obtain VWC where VWC: "set VWC = CVar -` (V - W)"
    by (meson assms finite_Diff finite_list finite_vimageI injI var.inject(2))

  define V1 where "V1 = V - CVar ` set VWC \<union> classical' (W-V)"

  have VW_V1: "idx12 (classical' (V - W)) \<inter> fvp (Eq0 V1) = {}"
    unfolding V1_def VWC apply (simp add: classical'_def flip: idx12_inter idx12_union)
    using is_classical.cases by blast

  have "R \<sqinter> Eq0 V1 = top \<sqinter> (R \<sqinter> Eq0 V1)"
    by simp
  also have "qRHL (top \<sqinter> (R \<sqinter> Eq0 V1))
            (Assign VWC some_constant) (Assign VWC some_constant)
            (Eq0 (CVar ` set VWC) \<sqinter> (R \<sqinter> Eq0 V1))"
    apply (rule frame_rule[rotated -1])
        apply (rule assign_Eq)
    using VW_R VW_V1
    by (auto intro!: program.intros fvp_inter_empty simp: X_inter_CVar VWC classical'_def idx12_def simp flip: idx.simps)
  also have "\<dots> \<le> Eq0 (CVar ` set VWC) \<sqinter> (R \<sqinter> (Eq0 (V - CVar ` set VWC)))"
    unfolding V1_def
    apply (subst Eq_split')
    apply (simp add: classical'_def is_classical'_def)
    by (metis inf_assoc inf_le1)
  also have "\<dots> = R \<sqinter> Eq0 V"
    apply (subst (2) asm_rl[of "V = (CVar ` set VWC) \<union> (V - CVar ` set VWC)"])
    apply (auto simp: VWC)[1]
    apply (subst Eq_split)
    apply (simp add: is_classical'_def)
    using inf_left_commute by blast
  also note qrhl
  also have "Seq (Assign VWC some_constant) c =d= c"
    apply (rule denot_eq_init)
    using VW_overwr by (auto simp add: classical'_def VWC)
  also have "Seq (Assign VWC some_constant) d =d= d"
    apply (rule denot_eq_init)
    using VW_overwr by (auto simp add: classical'_def VWC)
  finally have qrhl_V1: "qRHL (R \<sqinter> Eq0 V1) c d B"
    by (auto intro!: program.intros)

  define V2 where "V2 = V1 - quantum' (V-W)"

  obtain VWQ where VWQ: "set VWQ = QVar -` (V - W)" and "distinct VWQ"
    by (meson assms finite_Diff finite_distinct_list finite_vimageI injI var.simps(1))

  have VW_V2: "idx12 (quantum' (V - W)) \<inter> fvp (Eq0 V2) = {}"
    unfolding V2_def by (simp flip: idx12_inter)
  have V1_V2: "V1 = V2 \<union> QVar ` set VWQ"
    unfolding V2_def V1_def quantum'_def classical'_def VWC VWQ apply auto
    by (metis rangeI var.exhaust)

  have "R \<sqinter> Eq0 V2 = top \<sqinter> (R \<sqinter> Eq0 V2)"
    by simp
  also have "qRHL (top \<sqinter> (R \<sqinter> Eq0 V2))
            (QInit VWQ some_constant) (QInit VWQ some_constant)
            (Eq0 (QVar ` set VWQ) \<sqinter> (R \<sqinter> Eq0 V2))"
    apply (rule frame_rule[rotated -1])
    using \<open>distinct VWQ\<close> apply (rule qinit_Eq)
    using VW_R VW_V2 
    by (auto intro!: fvp_inter_empty program.intros simp: X_inter_QVar VWQ quantum'_def idx12_def simp flip: idx.simps)
  also have "\<dots> \<le> R \<sqinter> Eq0 (V2 \<union> QVar ` set VWQ)"
    apply (subst asm_rl[of "Eq0 (QVar ` set VWQ) \<sqinter> (R \<sqinter> Eq0 V2) = R \<sqinter> (Eq0 V2 \<sqinter> Eq0 (QVar ` set VWQ))"])
     apply (simp add: boolean_algebra_cancel.inf2 inf_sup_aci(1))
    apply (rule inf_mono, simp)
    apply (rule Eq_split_leq)
    using VW_V2 
    apply (auto intro!: fvp_inter_empty simp: quantum'_def idx12_def VWQ simp flip: idx.simps)
    by (metis (no_types, lifting) Diff_Diff_Int Diff_iff Un_iff empty_iff imageI is_classical.cases mem_Collect_eq var.distinct(1))
  also have "\<dots> = R \<sqinter> Eq0 V1"
    using V1_V2 by simp
  also note qrhl_V1
  also have "QInit VWQ some_constant; c =d= c"
    using \<open>distinct VWQ\<close> apply (rule denot_eq_qinit)
    unfolding VWQ using VW_overwr by auto
  also have "QInit VWQ some_constant; d =d= d"
    using \<open>distinct VWQ\<close> apply (rule denot_eq_qinit)
    unfolding VWQ using VW_overwr by auto
  finally have qrhl_V2: "qRHL (R \<sqinter> Eq0 V2) c d B"
    by (auto intro!: program.intros)

  define V3 where "V3 = V2 \<union> quantum' (W-V)"
  obtain WVQ where WVQ: "set WVQ = QVar -` (W - V)" and "distinct WVQ"
    by (meson assms finite_Diff finite_distinct_list finite_vimageI injI var.simps(1))

  have V2_V3: "V2 = quantum' V3 - QVar ` set WVQ \<union> classical' V3"
    unfolding V2_def V3_def quantum'_def classical'_def WVQ V1_def
    apply auto
    by (metis (full_types) is_classical.simps rangeI var.exhaust)

  have "R \<sqinter> Eq0 V3 = Eq0 (quantum' V3) \<sqinter> (R \<sqinter> Eq0 (classical' V3))"
    apply (subst asm_rl[of "V3 = quantum' V3 \<union> classical' V3"])
    apply (auto simp: quantum'_def classical'_def)[1]
    apply (subst Eq_split')
    apply (simp add: classical'_def is_classical'_def)
    by (simp add: inf_left_commute)
  also have "qRHL (Eq0 (quantum' V3) \<sqinter> (R \<sqinter> Eq0 (classical' V3)))
            (QInit WVQ some_constant) (QInit WVQ some_constant)
            (Eq0 (quantum' V3 - QVar ` set WVQ) \<sqinter> (R \<sqinter> Eq0 (classical' V3)))"
    apply (rule frame_rule[rotated -1])
      apply (rule joint_init_eq0)
       apply (metis Un_upper2 V3_def WVQ X_inter_QVar image_vimage_eq inf.bounded_iff inf_le2)
      apply (simp add: is_quantum'_def quantum'_def)
     apply (auto simp: WVQ quantum'_def classical'_def simp flip: idx.simps intro!: fvp_inter_empty program.intros)
    using WV_R unfolding quantum'_def idx12_def apply fastforce
      apply (metis (no_types, lifting) UnE idx_inj imageE is_classical_QVar mem_Collect_eq)
    using WV_R unfolding quantum'_def idx12_def apply fastforce
    by (metis (no_types, lifting) UnE idx_inj imageE is_classical_QVar mem_Collect_eq)
  also have "\<dots> = R \<sqinter> Eq0 (quantum' V3 - QVar ` set WVQ \<union> classical' V3)"
    apply (subst Eq_split')
    apply (simp add: classical'_def is_classical'_def)
    using inf_sup_aci(3) by blast
  also have "\<dots> = R \<sqinter> Eq0 V2"
    unfolding V2_V3 by simp
  also note qrhl_V2
  also have "QInit WVQ some_constant; c =d= c"
    using \<open>distinct WVQ\<close> apply (rule denot_eq_qinit)
    using WV_overwr by (auto simp add: WVQ quantum'_def)
  also have "QInit WVQ some_constant; d =d= d"
    using \<open>distinct WVQ\<close> apply (rule denot_eq_qinit)
    using WV_overwr by (auto simp add: WVQ quantum'_def)
  finally have qrhl_V3: "qRHL (R \<sqinter> Eq0 V3) c d B"
    by (auto intro!: program.intros)

  have "V3 = W"
    unfolding V3_def V2_def V1_def VWC classical'_def quantum'_def
    using is_classical.simps by auto

  with qrhl_V3 show ?thesis
    by simp
qed

lemma fv_vars: "fv C \<subseteq> vars C"
  by (induction C, auto)

lemma finite_vars[simp]: "finite (vars C)"
  by (induction C, auto)

lemma compatible_refl[simp]: "compatible x x"
  using compatible_sym compatible_trans compatible_inexhaust
  using not_finite_existsD by blast

lemma compatible_idx[simp]: \<open>compatible x y \<Longrightarrow> compatible (idx b x) (idx c y)\<close>
  by (meson compatible_idx compatible_sym compatible_trans)

lemma clean_CVar_case: "is_classical x \<Longrightarrow> CVar (case x of CVar x' \<Rightarrow> x' | QVar q \<Rightarrow> F q) = x" for x F
  using is_classical.simps by auto
lemma clean_QVar_case: "is_quantum x \<Longrightarrow> QVar (case x of QVar x' \<Rightarrow> x' | CVar q \<Rightarrow> F q) = x" for x F
    by (metis (full_types) is_classical.simps var.exhaust var.simps(5))

lemma finite_holes[simp]: "finite (holes C)"
  apply (induction C) by auto

lemma var_subst_dom_transpose[simp]: \<open>var_subst_dom (transpose x y) = {x,y}\<close> if \<open>x \<noteq> y\<close>
  using that by (auto simp: var_subst_dom_def transpose_def)

lemma subst_vars_rm_valid[simp]: 
  assumes "valid_var_subst \<sigma>"
  shows "valid_var_subst (\<sigma>(v:=v))"
  using assms unfolding valid_var_subst_def by simp

lemma valid_var_subst_transpose[simp]:
  assumes \<open>compatible x y\<close>
  shows \<open>valid_var_subst (transpose x y)\<close>
  using assms unfolding valid_var_subst_def
  by (metis compatible_refl compatible_sym transpose_def)

lemma valid_var_subst_id[simp]: \<open>valid_var_subst id\<close>
  by (simp add: valid_var_subst_def)

lemma subst_vars_v_classical:
  assumes "valid_var_subst \<sigma>"
  assumes "is_classical v"
  shows "is_classical (\<sigma> v)"
  using assms(1) assms(2) compatible_is_classical valid_var_subst_def by blast

lemma subst_vars_v_quantum:
  assumes "valid_var_subst \<sigma>"
  assumes "is_quantum v"
  shows "is_quantum (\<sigma> v)"
  using assms using compatible_is_classical valid_var_subst_def by blast

lemma subst_vars_c_compose[simp]:
  assumes "valid_var_subst \<tau>"
  shows "subst_vars_c \<sigma> (subst_vars_c \<tau> p) = subst_vars_c (\<sigma> o \<tau>) p"
  unfolding subst_vars_c_def apply auto
  apply (subst clean_CVar_case)
  apply (simp add: assms subst_vars_v_classical)
  by (rule refl)


lemma subst_vars_q_compose[simp]:
  assumes "valid_var_subst \<tau>"
  shows "subst_vars_q \<sigma> (subst_vars_q \<tau> p) = subst_vars_q (\<sigma> o \<tau>) p"
  unfolding subst_vars_q_def apply auto
  apply (subst clean_QVar_case)
  apply (simp add: assms subst_vars_v_quantum)
  by (rule refl)


lemma full_subst_vars_compose[simp]:
  assumes [simp]: "valid_var_subst \<tau>"
  shows "full_subst_vars \<sigma> (full_subst_vars \<tau> p) = full_subst_vars (\<sigma> o \<tau>) p"
  apply (induction p)
  by (auto simp: o_def)

lemma full_subst_vars_cong:
  assumes [simp]: "valid_var_subst \<sigma>"
  assumes "\<And>x. x\<in>vars p \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "full_subst_vars \<sigma> p = full_subst_vars \<tau> p"
  apply (insert assms, induction p)
  by (auto simp: subst_vars_q_def subst_vars_c_def intro!: subst_vars_e_cong)

lemma subst_vars_cong:
  assumes [simp]: "valid_var_subst \<sigma>"
  assumes "\<And>x. x\<in>fv p \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "subst_vars \<sigma> p = subst_vars \<tau> p"
proof (insert assms, induction p arbitrary: \<sigma> \<tau>)
  case (Local x p)
  have *: "y \<in> fv p \<Longrightarrow> (\<sigma>(x:=x)) y = (\<tau>(x:=x)) y" for y
    using Local.prems(2)[of y] by auto
  show ?case
    apply simp
    apply (rule Local.IH)
    using Local.prems(1) apply (rule subst_vars_rm_valid)
    using * by simp
qed (auto simp: subst_vars_q_def subst_vars_c_def intro!: subst_vars_e_cong)

lemma substitute_full_subst_vars_Skip[simp]:
  "substitute (full_subst_vars \<sigma> c) (\<lambda>_. Skip) = full_subst_vars \<sigma> (substitute c (\<lambda>_. Skip))"
  apply (induction c) by auto

lemma full_subst_vars_id:
  assumes "bij \<sigma>"
  assumes "valid_var_subst \<sigma>"
  assumes "var_subst_dom \<sigma> \<inter> fv c = {}"
  shows "full_subst_vars \<sigma> c =d= c"
  unfolding denot_eq'_def apply simp
  apply (rule full_subst_vars_id0)
  using assms by (auto simp: program.intros(3) program_substitute)

lemma vars_full_subst_vars:
  assumes "valid_var_subst \<sigma>"
  shows "vars (full_subst_vars \<sigma> p) = \<sigma> ` vars p"
  apply (induction p)
  by (simp_all add: image_image image_Un subst_vars_c_def
                    fve_subst_vars_e[OF assms] subst_vars_q_def
                    clean_CVar_case[OF subst_vars_v_classical[OF assms]]
                    clean_QVar_case[OF subst_vars_v_quantum[OF assms]])


lemma subst_vars_id[simp]:
  shows "subst_vars (\<lambda>x. x) c = c"
  by (induction c, auto simp: subst_vars_c_def[abs_def] subst_vars_q_def[abs_def] fun_upd_def)


lemma subst_vars_idI:
  assumes "valid_var_subst \<sigma>"
  assumes "fv c \<inter> var_subst_dom \<sigma> = {}"
  shows "subst_vars \<sigma> c = c"
  apply (subst (3) subst_vars_id[symmetric])
  apply (rule subst_vars_cong)
  using assms unfolding var_subst_dom_def by auto


inductive_cases
  ic_nc_Local: "no_conflict \<sigma> (Local v c)"
  and ic_nc_IfTE: "no_conflict \<sigma> (IfTE e c1 c2)"
  and ic_nc_Seq: "no_conflict \<sigma> (c1; c2)"
  and ic_nc_While: "no_conflict \<sigma> (While e c)"

lemma subst_vars_compose:
  assumes "valid_var_subst f"
  assumes "valid_var_subst g"
  assumes "no_conflict g c"
  shows "subst_vars f (subst_vars g c) = subst_vars (f o g) c"
  using assms
proof (induction c arbitrary: f g)
  case (Local x c)
  from Local.prems have no: "no_conflict g (Local x c)"
    by simp
  then have no': "no_conflict (g(x := x)) c"
    by (rule ic_nc_Local)

  from Local.prems
  have validf: "valid_var_subst (f(x := x))" and validg: "valid_var_subst (g(x := x))"
    unfolding valid_var_subst_def by auto
  then have validfg: "valid_var_subst (f(x := x) \<circ> g(x := x))"
    by (metis comp_apply compatible_trans valid_var_subst_def)

  have *: "(f(x := x) \<circ> g(x := x)) y = ((f o g)(x := x)) y" if "y \<in> fv c" for y
    using no apply (rule ic_nc_Local)
    using that var_subst_dom_def
    by fastforce

  show ?case 
    apply simp
    apply (subst Local.IH[OF validf validg no'])
    using validfg apply (rule subst_vars_cong)
    using * by (auto simp: o_def)
next
  case (IfTE e c1 c2)
  show ?case
    apply simp
    apply (subst IfTE.IH)
    using IfTE.prems apply (auto simp: o_def intro: ic_nc_IfTE)[3]
    apply (subst IfTE.IH)
    using IfTE.prems by (auto simp: o_def intro: ic_nc_IfTE)
next
  case Seq
  show ?case 
    apply simp
    apply (subst Seq.IH)
    using Seq.prems apply (auto simp: o_def intro: ic_nc_Seq)[3]
    apply (subst Seq.IH)
    using Seq.prems by (auto simp: o_def intro: ic_nc_Seq)
qed (auto simp: o_def intro: ic_nc_While)

lemma valid_var_subst_comp[intro]:
  "valid_var_subst f \<Longrightarrow> valid_var_subst g \<Longrightarrow> valid_var_subst (f \<circ> g)"
  unfolding valid_var_subst_def apply auto
  using compatible_trans by blast

lemma fresh_compatible:
  assumes "finite {x. \<not> P x}"
  shows "\<exists>y. compatible x y \<and> P y"
  using Collect_mono_iff assms compatible_inexhaust infinite_super by fastforce


lemma size_full_subst_vars[simp]:
  "size (full_subst_vars f c) = size c"
  by (induction c, auto)

lemma finite_localvars[simp]: "finite (localvars c)"
  by (induction c, auto)


lemma localvars_vars: "localvars c \<subseteq> vars c"
  by (induction c, auto)

lemma localvars_full_subst_vars[simp]: "localvars (full_subst_vars f c) = f ` localvars c"
  by (induction c, auto)


lemma avoiding_subst:
  assumes \<open>finite V\<close> \<open>finite avoid\<close>
  obtains \<sigma>1 :: "var \<Rightarrow> var" 
    where "valid_var_subst \<sigma>1"
    and "inj_on \<sigma>1 V"
    and "var_subst_dom \<sigma>1 \<subseteq> V"
    and "\<sigma>1 ` V \<inter> avoid = {}"
  apply atomize_elim using \<open>finite V\<close> \<open>finite avoid\<close>
proof (induction V arbitrary: avoid)
  case empty
  show ?case 
    apply (rule exI[of _ id])
    by (auto simp add: var_subst_dom_def valid_var_subst_def)
next
  case (insert x F)

  from \<open>finite avoid\<close>
  obtain y where compat: "compatible x y" and avoid_y: "y \<notin> avoid"
    by (atomize_elim, rule_tac fresh_compatible, simp)

  from \<open>finite avoid\<close>
  have "finite (insert y avoid)"
    by simp
  from insert.IH[OF this]
  obtain \<sigma>' where valid: "valid_var_subst \<sigma>'" and inj: "inj_on \<sigma>' F" 
    and dom: "var_subst_dom \<sigma>' \<subseteq> F" and avoid: "\<sigma>' ` F \<inter> insert y avoid = {}"
    by auto

  define \<sigma>1 where "\<sigma>1 = \<sigma>' (x:=y)"

  from valid have "valid_var_subst \<sigma>1"
    unfolding \<sigma>1_def
    by (simp add: compat valid_var_subst_def)

  moreover
  have "inj_on \<sigma>1 (insert x F)"
    apply (rule_tac inj_on_insert[THEN iffD2])
    unfolding \<sigma>1_def apply auto
     apply (metis fun_upd_other inj inj_on_cong insert.hyps(2))
    using avoid by auto

  moreover
  from dom 
  have "var_subst_dom \<sigma>1 \<subseteq> insert x F"
    unfolding \<sigma>1_def var_subst_dom_def by auto

  moreover  
  have "\<sigma>1 ` insert x F \<inter> avoid = {}"
    unfolding \<sigma>1_def using avoid avoid_y by auto

  ultimately show ?case
    by auto
qed


lemma subst_bij_id'[simp]: "substp_bij id A = A"
  by (rule substp_bij_id, auto)

lemma extend_var_subst:
  assumes "inj_on \<sigma> V"
  assumes "valid_var_subst \<sigma>"
  assumes "finite V"
  obtains \<tau> where "bij \<tau>" and "valid_var_subst \<tau>" and "\<forall>x\<in>V. \<tau> x = \<sigma> x"
proof -
  obtain V' where V': "V = set V'" and "distinct V'"
    using \<open>finite V\<close> finite_distinct_list by blast
  define W W' VW where "W = \<sigma> ` V" and "W' = map \<sigma> V'" and "VW = V \<union> W"

  have \<open>finite VW\<close>
    by (simp add: VW_def W_def assms(3))
  then obtain Z' where compatVZ: "list_all2 compatible V' Z'"
    and "distinct Z'" and "set Z' \<inter> VW = {}"
    apply atomize_elim
  proof (induction V' arbitrary: VW)
    case Nil
    show ?case by auto
  next
    case (Cons x V'')
    obtain Z'' where compat: "list_all2 compatible V'' Z''" and "distinct Z''" 
      and disj: "set Z'' \<inter> insert x VW = {}"
      using Cons.IH Cons.prems by blast
    obtain y where [simp]: "compatible x y" and "y \<notin> VW" and "y \<notin> set Z''"
      apply atomize_elim apply (rule fresh_compatible) 
      using Cons.prems by auto 
    define Z' V' where "Z' = y # Z''" and "V' = x # V''"
    have "list_all2 compatible V' Z'"
      unfolding V'_def Z'_def using compat by auto
    moreover have "distinct Z'"
      unfolding Z'_def using \<open>distinct Z''\<close> \<open>y \<notin> set Z''\<close> by auto
    moreover have "set Z' \<inter> VW = {}"
      unfolding Z'_def using \<open>y \<notin> VW\<close> disj by auto
    ultimately show ?case
      apply (rule_tac exI[of _ Z'])
      by (auto simp: V'_def)
  qed

  define f ok where "f X Y a = (if a \<in> set X then Y ! (SOME i. X!i=a \<and> i<length X) 
                          else if a \<in> set Y then X ! (SOME i. Y!i=a \<and> i<length Y)
                          else a)"
    and "ok X Y \<longleftrightarrow> length X = length Y \<and> distinct X \<and> distinct Y \<and> set X \<inter> set Y = {}"
  for X Y and a :: var
  have idx[simp]: "(SOME i. X!i=X!j \<and> i<length X) = j" if "distinct X" and "j<length X" for X :: "var list" and j
  proof -
    have "X!(SOME i. X!i=X!j \<and> i<length X) = X!j \<and> (SOME i. X!i=X!j \<and> i<length X) < length X"
      apply (rule someI) using that by simp
    then show ?thesis
      apply (rule_tac nth_eq_iff_index_eq[THEN iffD1])
      using that by auto
  qed
  have evalf1: "f X Y (X!i) = Y!i" if "ok X Y" and [simp]: "i < length X" for X Y i
    unfolding f_def using that unfolding ok_def by (subst idx, auto)
  have evalf2: "f X Y (Y!i) = X!i" if "ok X Y" and [simp]: "i < length X" for X Y i
    unfolding f_def using that unfolding ok_def by (subst idx, auto)
  have evalf3: "f X Y a = a" if "a \<notin> set X \<union> set Y" for X Y a
    unfolding f_def using that by auto
  have f_idem: "f X Y \<circ> f X Y = id" if "ok X Y" for X Y
  proof (rule ext, simp)
    fix a
    consider (X) i where "a = X!i" "i < length X" | (Y) i where "a = Y!i" "i < length Y" | (none) "a \<notin> set X \<union> set Y"
      apply auto by (metis in_set_conv_nth)
    then show "f X Y (f X Y a) = a"
      apply cases
      using that by (auto simp add: evalf1 evalf2 evalf3 ok_def)
  qed
  then have bij_f: "bij (f X Y)" if "ok X Y" for X Y
    using o_bij that by auto
  have all_f1: "R a (f X Y a)" if "ok X Y" and all2: "list_all2 R X Y" and "a \<in> set X" for R X Y a
  proof -
     obtain i where i: "i < length X" and Xi: "X!i = a"
      using \<open>a \<in> set X\<close> by (meson in_set_conv_nth)
    then have *: "f X Y a = Y!i"
      using \<open>ok X Y\<close> evalf1 by blast
    have "R (X!i) (Y!i)"
      using all2 i by (simp add: list_all2_nthD)
    with Xi * show ?thesis
      by simp
  qed
  have all_f2: "R a (f X Y a)" if "ok X Y" and all2: "list_all2 R X Y" 
    and "a \<in> set Y" and "symp R" for R X Y a
  proof -
     obtain i where i: "i < length Y" and Yi: "Y!i = a"
      using \<open>a \<in> set Y\<close> by (meson in_set_conv_nth)
    then have *: "f X Y a = X!i"
      using evalf2 ok_def that(1) by auto
    have "R (X!i) (Y!i)"
      using all2 i
      by (simp add: list_all2_nthD2)
    with Yi * \<open>symp R\<close> show ?thesis
      using sympD by fastforce
  qed
  have all_f3: "R a (f X Y a)" if "ok X Y" and \<open>reflp R\<close> 
    and "a \<notin> set X \<union> set Y" for R X Y a
    using that apply (simp add: evalf3)
    by (simp add: reflpD)
  have all_f: "R a (f X Y a)" if "ok X Y" and \<open>list_all2 R X Y\<close> and \<open>reflp R\<close> and \<open>symp R\<close> for X Y R a
    using all_f1 all_f2 all_f3 that by fastforce

  have [simp]: "ok V' Z'"
    unfolding ok_def
    by (metis Int_Un_distrib VW_def \<open>V = set V'\<close> \<open>distinct V'\<close> \<open>distinct Z'\<close> \<open>set Z' \<inter> VW = {}\<close> bot_eq_sup_iff compatVZ inf.commute list_all2_lengthD)
  have [simp]: "ok Z' W'"
    by (metis Int_Un_distrib VW_def W'_def W_def \<open>V = set V'\<close> \<open>distinct V'\<close> \<open>distinct Z'\<close> \<open>set Z' \<inter> VW = {}\<close> assms(1) bot_eq_sup_iff compatVZ distinct_map length_map list_all2_lengthD ok_def set_map)
  have compatZW: "list_all2 compatible Z' W'"
    using compatVZ unfolding W'_def
    by (smt assms(2) compatible_sym compatible_trans length_map list_all2_conv_all_nth nth_map valid_var_subst_def)

  define \<tau> where "\<tau> = f Z' W' \<circ> f V' Z'"

  have "bij \<tau>"
    unfolding \<tau>_def apply (rule bij_comp)
    by (rule bij_f, simp)+
  moreover
  have "valid_var_subst \<tau>"
  proof -
    have "valid_var_subst (f V' Z')"
      unfolding valid_var_subst_def apply auto
      by (rule all_f, auto simp: compatVZ reflpI compatible_sym sympI)
    moreover have "valid_var_subst (f Z' W')"
      unfolding valid_var_subst_def apply auto
      by (rule all_f, auto simp: compatZW reflpI compatible_sym sympI)
    ultimately show ?thesis
      unfolding \<tau>_def by auto
  qed
  moreover have "\<tau> a = \<sigma> a" if a: "a\<in>V" for a
  proof -
     obtain i where i: "i < length V'" and V'i: "V'!i = a"
      using a unfolding V' by (meson in_set_conv_nth)
    then have "f V' Z' a = Z'!i"
      using \<open>ok V' Z'\<close> evalf1 by blast
    then have "f Z' W' (f V' Z' a) = W'!i"
      using \<open>i < length V'\<close> \<open>ok V' Z'\<close> \<open>ok Z' W'\<close> evalf1 ok_def by auto
    also have "W'!i = \<sigma> a"
      unfolding W'_def V'i[symmetric] using i by auto
    finally show ?thesis
      unfolding \<tau>_def by simp
  qed

  ultimately show ?thesis
    using that by auto
qed

lemma substp_substp_bij:
  assumes "bij \<tau>" and "valid_var_subst \<tau>" and "\<forall>x\<in>fvp A. \<tau> x = \<sigma> x"
  shows "substp \<sigma> A = substp_bij \<tau> A"
proof -
  define \<tau>' where "\<tau>' = (SOME \<tau>. bij \<tau> \<and> valid_var_subst \<tau> \<and> (\<forall>x\<in>fvp A. \<tau> x = \<sigma> x))"
  have "bij \<tau>' \<and> valid_var_subst \<tau>' \<and> (\<forall>x\<in>fvp A. \<tau>' x = \<sigma> x)"
    unfolding \<tau>'_def apply (rule someI[where P=\<open>\<lambda>\<tau>. bij \<tau> \<and> valid_var_subst \<tau> \<and> (\<forall>x\<in>fvp A. \<tau> x = \<sigma> x)\<close>])
    using assms by simp
  then have "bij \<tau>'" and "valid_var_subst \<tau>'" and \<tau>'_\<sigma>: "\<forall>x\<in>fvp A. \<tau>' x = \<sigma> x"
    by auto
  define \<gamma> where "\<gamma> = inv \<tau> \<circ> \<tau>'"
  then have \<tau>_alt_def: "\<tau>' = \<tau> \<circ> \<gamma>"
    using \<open>bij \<tau>\<close>
    by (simp add: bij_betw_def fun.map_comp surj_iff)
  have "valid_var_subst \<gamma>"
    using \<open>valid_var_subst \<tau>'\<close> \<open>valid_var_subst \<tau>\<close>
    unfolding \<gamma>_def valid_var_subst_def apply auto
    by (metis assms(1) bijection.inv_right bijection_def compatible_sym compatible_trans)
  have \<gamma>_id: "x \<in> fvp A \<Longrightarrow> \<gamma> x = x" for x
    unfolding \<gamma>_def
    by (simp add: \<tau>'_\<sigma> assms(1) assms(3) bij_is_inj inv_f_eq)
  have "bij \<gamma>"
    unfolding \<gamma>_def using \<open>bij \<tau>\<close> \<open>bij \<tau>'\<close>
    using bij_betw_trans bij_imp_bij_inv by blast

  have sub\<sigma>_sub\<tau>': "substp \<sigma> A = substp_bij \<tau>' A"
    unfolding substp_def \<tau>'_def by simp
  also have "\<dots> = substp_bij \<tau> (substp_bij \<gamma> A)"
    unfolding \<tau>_alt_def
    apply (subst substp_bij_comp)
    using \<open>valid_var_subst \<gamma>\<close> \<open>valid_var_subst \<tau>\<close> \<open>bij \<gamma>\<close> \<open>bij \<tau>\<close>
    by auto
  also have "\<dots> = substp_bij \<tau> A"
    apply (subst (2) substp_bij_id)
    using \<open>valid_var_subst \<gamma>\<close> \<gamma>_id \<open>bij \<gamma>\<close> by auto
  finally show ?thesis
    by -
qed

lemma substp_cong:
  assumes eq: "\<And>x. x \<in> fvp A \<Longrightarrow> \<sigma> x = \<tau> x"
  assumes valid: "valid_var_subst \<sigma>" "valid_var_subst \<tau>"
  assumes inj\<sigma>: "inj_on \<sigma> (fvp A)"
  shows "substp \<sigma> A = substp \<tau> A" 
proof -
  from inj\<sigma> eq have inj\<tau>: "inj_on \<tau> (fvp A)"
    using inj_on_cong by blast

  from valid inj\<sigma>
  obtain \<sigma>' where "bij \<sigma>'" and "valid_var_subst \<sigma>'" and eq\<sigma>: "\<forall>x\<in>fvp A. \<sigma>' x = \<sigma> x"
    using extend_var_subst by (metis finite_fvp)
  from valid inj\<tau>
  obtain \<tau>' where "bij \<tau>'" and "valid_var_subst \<tau>'" and eq\<tau>: "\<forall>x\<in>fvp A. \<tau>' x = \<tau> x"
    using extend_var_subst by (metis finite_fvp)
  define \<gamma> where "\<gamma> = inv \<tau>' \<circ> \<sigma>'"
  with \<open>bij \<tau>'\<close> have \<sigma>': "\<sigma>' = \<tau>' \<circ> \<gamma>"
    by (simp add: bijection.intro bijection.inv_comp_right o_assoc)
  with \<open>valid_var_subst \<sigma>'\<close> \<open>valid_var_subst \<tau>'\<close> have "valid_var_subst \<gamma>"
    by (metis comp_apply compatible_sym compatible_trans valid_var_subst_def)
  from \<gamma>_def \<open>bij \<tau>'\<close> eq eq\<sigma> eq\<tau>
  have \<gamma>_id: "\<gamma> x = x" if "x \<in> fvp A" for x
    by (simp add: bij_is_inj inv_f_eq that)
  have "bij \<gamma>"
    by (simp add: \<gamma>_def \<open>bij \<sigma>'\<close> \<open>bij \<tau>'\<close> bij_comp bijection.bij_inv bijection.intro)

  have "substp \<sigma> A = substp_bij \<sigma>' A"
    apply (rule substp_substp_bij)
    using \<open>bij \<sigma>'\<close> \<open>valid_var_subst \<sigma>'\<close> eq\<sigma> by auto
  also have "\<dots> = substp_bij \<tau>' (substp_bij \<gamma> A)"
    unfolding \<sigma>' 
    using \<open>bij \<sigma>'\<close> \<open>bij \<tau>'\<close> \<open>valid_var_subst \<gamma>\<close> \<open>valid_var_subst \<tau>'\<close>
    using \<gamma>_def bij_comp bij_imp_bij_inv substp_bij_comp by force
  also have "\<dots> = substp_bij \<tau>' A"
    apply (subst (2) substp_bij_id)
    using \<open>bij \<gamma>\<close> \<open>valid_var_subst \<gamma>\<close> \<open>valid_var_subst \<gamma>\<close>
    using \<gamma>_id by auto
  also have "\<dots> = substp \<tau> A"
    apply (rule substp_substp_bij[symmetric])
    using \<open>bij \<tau>'\<close> \<open>valid_var_subst \<tau>'\<close> eq\<tau> by auto
  finally show ?thesis
    by -
qed


lemma rename_qrhl1:
  assumes \<open>compatible (QVar q) (QVar r)\<close>
  assumes "QVar q \<notin> fv c"
  assumes "QVar r \<notin> fv c"
  assumes "qRHL A c d B"
  shows "qRHL (substp (transpose (idx True (QVar q)) (idx True (QVar r))) A) c d (substp (transpose (idx True (QVar q)) (idx True (QVar r))) B)"
  using assms program.intros(3) substp_substp_bij[where \<tau>=\<open>transpose (idx True (QVar q)) (idx True (QVar r))\<close>] program_substitute qRHL_def rename_qrhl10 
  by (auto simp del: idx.simps)
  
lemma rename_qrhl2:
  assumes \<open>compatible (QVar q) (QVar r)\<close>
  assumes "QVar q \<notin> fv d"
  assumes "QVar r \<notin> fv d"
  assumes "qRHL A c d B"
  shows "qRHL (substp (transpose (idx False (QVar q)) (idx False (QVar r))) A) c d (substp (transpose (idx False (QVar q)) (idx False (QVar r))) B)"
  using assms program.intros(3) substp_substp_bij[where \<tau>=\<open>transpose (idx False (QVar q)) (idx False (QVar r))\<close>] program_substitute qRHL_def rename_qrhl20 by (auto simp del: idx.simps)

lemma CVar_subst_vars_c[simp]: 
  assumes "valid_var_subst \<sigma>"
  shows "CVar (subst_vars_c \<sigma> x) = \<sigma> (CVar x)"
  using assms unfolding subst_vars_c_def valid_var_subst_def
  by (simp add: assms clean_CVar_case subst_vars_v_classical)

lemma QVar_subst_vars_q[simp]: 
  assumes "valid_var_subst \<sigma>"
  shows "QVar (subst_vars_q \<sigma> x) = \<sigma> (QVar x)"
  using assms unfolding subst_vars_q_def valid_var_subst_def
  by (simp add: assms clean_QVar_case subst_vars_v_quantum)

lemma fv_subst_vars:
  assumes "valid_var_subst \<sigma>"
  shows "fv (subst_vars \<sigma> c) \<subseteq> \<sigma> ` fv c"
  using assms
proof (induction c arbitrary: \<sigma>)
  case (Local x c)
  have IH: "fv (subst_vars (\<sigma>(x := x)) c) \<subseteq> \<sigma>(x := x) ` fv c"
    apply (rule Local.IH[where \<sigma>="\<sigma>(x := x)"])
    using Local.prems subst_vars_rm_valid by blast
  then show ?case
    by auto
qed (auto simp add: image_Un image_image, blast+)

lemma fv_subst_vars':
  assumes "valid_var_subst \<sigma>"
  assumes "no_conflict \<sigma> c"
  shows "fv (subst_vars \<sigma> c) = \<sigma> ` fv c"
  using assms
proof (induction c arbitrary: \<sigma>)
  case (Local x c)
  have IH: "fv (subst_vars (\<sigma>(x := x)) c) = \<sigma>(x := x) ` fv c"
    apply (rule Local.IH[where \<sigma>="\<sigma>(x := x)"])
    using Local.prems(1) subst_vars_rm_valid apply blast
    using Local.prems(2) ic_nc_Local by blast
  then show ?case
    apply auto
    by (smt Int_Collect Local.prems(2) ic_nc_Local image_eqI var_subst_dom_def)
next
  case IfTE
  then show ?case
    apply (auto simp add: image_Un image_image)
    apply (meson fv_subst_vars subset_iff)
    apply (meson fv_subst_vars subset_iff)
    apply (metis ic_nc_IfTE imageI)
    by (metis ic_nc_IfTE imageI)
next
  case While
  then show ?case
    apply (auto simp add: image_Un image_image)
    apply (meson fv_subst_vars subset_iff)
    using ic_nc_While by blast
next
  case Seq
  then show ?case
    apply (auto simp add: image_Un image_image)
    apply (meson fv_subst_vars subset_iff)
    apply (meson fv_subst_vars subset_iff)
    apply (metis ic_nc_Seq imageI)
    by (metis ic_nc_Seq imageI)
qed (auto simp add: image_Un image_image)


inductive_cases program_ind_cases:
  "program (IfTE e c d)"
  "program (While c d)"
  "program (Local x c)"
  "program (c; d)"

lemma program_full_subst_vars[simp]: "program (full_subst_vars \<sigma> c) = program c"
  by (induction c, auto intro: program.intros elim: program_ind_cases)

lemma subst_vars_c_id[simp]: "subst_vars_c id = id"
  unfolding subst_vars_c_def by auto

lemma subst_vars_q_id[simp]: "subst_vars_q id = id"
  unfolding subst_vars_q_def by auto

lemma full_subst_vars_id'[simp]: "full_subst_vars id = id"
  apply (rule ext, rename_tac c, induct_tac c)
  by (auto simp: subst_vars_c_id[unfolded id_def] subst_vars_q_id[unfolded id_def])

lemma vars_fv_localvars: "vars c = fv c \<union> localvars c"
  by (induction c, auto)

lemma fv_full_subst_vars: 
  assumes [simp]: "valid_var_subst \<sigma>"
  assumes "inj_on \<sigma> (vars c)"
  shows "fv (full_subst_vars \<sigma> c) = \<sigma> ` fv c"
  using assms(2)
  apply (induction c)
  apply (simp_all add: inj_on_Un image_Un image_image)
  by (smt Diff_subset Un_upper2 fv_vars image_empty image_insert inf_sup_aci(5) inj_on_image_set_diff inj_on_insert insert_def order_trans singleton_conv)




lemma full_subst_vars_subst_vars_eq: 
  assumes "var_subst_dom \<sigma> \<inter> localvars c = {}"
  shows "full_subst_vars \<sigma> c = subst_vars \<sigma> c"
  using assms apply (induction c)
  by (auto simp: var_subst_dom_def fun_upd_idem)

lemma full_subst_vars_subst_vars_comm:
  assumes [simp]: "bij \<tau>"
  assumes valid\<sigma>[simp]: "valid_var_subst \<sigma>"
  assumes valid\<tau>[simp]: "valid_var_subst \<tau>"
  shows "full_subst_vars \<tau> (subst_vars \<sigma> c) = subst_vars (\<tau> \<circ> \<sigma> \<circ> inv \<tau>) (full_subst_vars \<tau> c)"
  using valid\<sigma>
proof (induction c arbitrary: \<sigma>)
  case (Local x c)
  show ?case 
    apply simp
    apply (subst Local.IH)
    apply (simp add: Local.prems)
    by (metis assms(1) bij_inv_eq_iff comp_apply fun_upd_apply)
qed (auto simp: o_def inv_f_f bij_is_inj)

lemma no_conflict_full_subst_vars:
  assumes [simp]: "bij \<tau>"
  assumes [simp]: "valid_var_subst \<tau>"
  assumes "no_conflict \<sigma> c"
  shows "no_conflict (\<tau> \<circ> \<sigma> \<circ> inv \<tau>) (full_subst_vars \<tau> c)"
  using assms(3)
proof induction
  case (nc_Local \<sigma> v c)
  have [simp]: "inj_on \<tau> A" for A
    using assms
    using bij_is_inj inj_on_subset by blast
  have [simp]: "var_subst_dom (\<tau> \<circ> \<sigma> \<circ> inv \<tau>) = \<tau> ` var_subst_dom \<sigma>"
    unfolding var_subst_dom_def apply auto
    apply (smt assms(1) bij_inv_eq_iff mem_Collect_eq setcompr_eq_image)
    by (simp add: inj_eq)
  have *: "(\<tau> \<circ> \<sigma> \<circ> inv \<tau>)(\<tau> v := \<tau> v) = \<tau> \<circ> \<sigma>(v := v) \<circ> inv \<tau>"
    apply rule apply auto
    by (metis assms(1) bij_inv_eq_iff)
  have 1: "no_conflict ((\<tau> \<circ> \<sigma> \<circ> inv \<tau>)(\<tau> v := \<tau> v)) (full_subst_vars \<tau> c)"
    using nc_Local.IH unfolding * by -
  have 2: "\<tau> v \<notin> (\<tau> \<circ> \<sigma> \<circ> inv \<tau>) `
            (fv (full_subst_vars \<tau> c) \<inter> var_subst_dom (\<tau> \<circ> \<sigma> \<circ> inv \<tau>))"
    apply (simp only: image_comp[symmetric])
    apply (simp add: inj_image_mem_iff fv_full_subst_vars flip: image_Int)
    by (fact nc_Local)
  show ?case
    apply (simp only: full_subst_vars.simps)
    using 1 2 by (rule no_conflict.nc_Local)
qed (auto intro!: no_conflict.intros)

lemma no_conflict_full_subst_vars':
  assumes [simp]: "bij \<tau>"
  assumes [simp]: "valid_var_subst \<tau>"
  assumes "no_conflict (inv \<tau> \<circ> \<sigma> \<circ> \<tau>) c"
  shows "no_conflict \<sigma> (full_subst_vars \<tau> c)"
  apply (subst asm_rl[of "\<sigma> = \<tau> \<circ> (inv \<tau> \<circ> \<sigma> \<circ> \<tau>) \<circ> inv \<tau>"])
  apply (metis assms(1) bijection.intro bijection.inv_comp_right comp_assoc comp_id fun.map_id)
  using assms by (rule no_conflict_full_subst_vars)

lemma no_conflict_cong:
  assumes "\<And>x. x \<in> fv c \<Longrightarrow> \<sigma> x = \<tau> x"
  assumes "no_conflict \<sigma> c"
  shows "no_conflict \<tau> c"
  using assms(2,1)
proof (induction arbitrary: \<tau>)
  case (nc_Local \<sigma> v c)
  then show ?case 
    apply auto
    by (smt Int_iff fun_upd_other fun_upd_same image_iff mem_Collect_eq no_conflict.nc_Local var_subst_dom_def)
qed (auto simp: no_conflict.intros)

lemma localvars_subst_vars[simp]:
  shows "localvars (subst_vars \<sigma> c) = localvars c"
  by (induction c arbitrary: \<sigma>, auto)


lemma no_conflict_remove: 
  assumes "no_conflict \<sigma> c"
  shows "no_conflict (\<sigma>(x:=x)) c"
  using assms
proof (induction)
  case (nc_Local \<sigma> v c)
  show ?case
    apply (rule no_conflict.intros)
     apply (metis nc_Local.IH fun_upd_twist) 
    using nc_Local by (simp add: image_iff var_subst_dom_def)
qed (auto simp: no_conflict.intros)

lemma localvars_dom_no_conflict:
  assumes "localvars c \<inter> \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>) = {}"
  shows "no_conflict \<sigma> c"
  using assms
proof (induction c arbitrary: \<sigma>)
  case (Local x c)
  have "no_conflict (\<sigma>(x := x)) c"
    apply (rule Local.IH)
    using Local.prems
    by (auto simp add: var_subst_dom_def)
  moreover have "x \<notin> \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>)"
    using Local.prems
    by (auto simp add:  var_subst_dom_def)
  ultimately show ?case
    by (rule no_conflict.intros)
qed (auto intro!: no_conflict.intros)

lemma fv_foldr_Local[simp]: "fv (foldr Local V c) = fv c - set V"
  by (induction V, auto)

lemma valid_var_subst_idx[simp]: 
  assumes "valid_var_subst \<tau>"
  shows "valid_var_subst (idx_var_subst side \<tau>)"
  using assms unfolding valid_var_subst_def idx_var_subst_def
  by auto

lemma inj_idx_var_subst[simp]:
  assumes "inj \<tau>"
  shows "inj (idx_var_subst side \<tau>)"
  using assms unfolding inj_def idx_var_subst_def
  by (metis idx_inj inv_into_injective range_eqI)


lemma inj_on_idx_var_subst1[simp]:
  assumes "NO_MATCH UNIV X"
  assumes "inj_on \<tau> (deidx side X)"
  shows "inj_on (idx_var_subst side \<tau>) X"
proof (rule inj_onI)
  fix x y assume "x \<in> X" and "y \<in> X"
  assume eq: "idx_var_subst side \<tau> x = idx_var_subst side \<tau> y"

  consider (x) "x \<in> range (idx side)" "y \<notin> range (idx side)"
    | (y) "y \<in> range (idx side)" "x \<notin> range (idx side)"
    | (xy) "y \<in> range (idx side)" "x \<in> range (idx side)"
    | (none) "y \<notin> range (idx side)" "x \<notin> range (idx side)"
    by metis
  then show "x = y"
  proof cases
    case x
    with eq show ?thesis 
      unfolding idx_var_subst_def by auto
  next
    case y
    with eq show ?thesis 
      unfolding idx_var_subst_def by auto
  next
    case xy
    with eq show ?thesis 
      unfolding idx_var_subst_def using assms
      unfolding deidx_def apply auto
      using \<open>x \<in> X\<close> \<open>y \<in> X\<close> inv_into_f_f by fastforce
  next
    case none
    with eq show ?thesis
      unfolding idx_var_subst_def by auto
  qed
qed

lemma surj_idx_var_subst[simp]:
  assumes "surj \<tau>"
  shows "surj (idx_var_subst side \<tau>)"
  using assms unfolding surj_def idx_var_subst_def
  by (metis (no_types, lifting) f_inv_into_f idx_inj' range_eqI range_ex1_eq)

lemma bij_idx_var_subst[simp]:
  assumes "bij \<tau>"
  shows "bij (idx_var_subst side \<tau>)"
  using assms unfolding bij_def 
  by auto

lemma inv_idx_var_subst:
  assumes [simp]: "bij \<tau>"
  shows "inv (idx_var_subst side \<tau>) = idx_var_subst side (inv \<tau>)"
proof -
  have "idx_var_subst side \<tau> (idx_var_subst side (inv \<tau>) x) = x" for x
    apply (auto simp add: inj_def idx_var_subst_def)
    by (meson assms bij_inv_eq_iff)
  then show ?thesis
    apply (rule_tac inj_imp_inv_eq)
    by (auto simp add: bij_is_inj)
qed

lemma var_subst_dom_idx_var_subst[simp]:
  "var_subst_dom (idx_var_subst side \<sigma>) = idx side ` var_subst_dom \<sigma>"
  unfolding var_subst_dom_def idx_var_subst_def by auto

lemma finite_deidx[simp]: "finite X \<Longrightarrow> finite (deidx side X)"
  unfolding deidx_def
  by (metis (full_types) Un_infinite finite_fvp finite_imageD fvp_Eq idx12_def idx_inj' sup_top_right) 

lemma no_conflict_locals:
  assumes "finite X"
  assumes "no_conflict (\<lambda>x. if x \<in> X then x else \<sigma> x) c"
  assumes "X \<inter> \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>) = {}"
  shows "no_conflict \<sigma> (locals X c)"
  using \<open>finite X\<close>
proof (rule locals.F_intro)
  fix X' assume X': "set X' = X" assume "distinct X'"
  show "no_conflict \<sigma> (foldr Local X' c)"
    using assms(2,3) unfolding X'[symmetric]
  proof (induction X' arbitrary: \<sigma>)
    case Nil then show ?case by simp
  next
    case (Cons x X)
    then have nc: "no_conflict (\<lambda>y. if y \<in> set (x # X) then y else \<sigma> y) c"
      and disj: "set (x # X) \<inter> \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>) = {}"
      by -

    have disj': "set X \<inter> \<sigma>(x := x) ` (fv c \<inter> var_subst_dom (\<sigma>(x := x))) = {}"
      using disj by (auto simp: var_subst_dom_def)

    from nc have nc': "no_conflict (\<lambda>y. if y \<in> set X then y else (\<sigma>(x := x)) y) c"
      apply (rule no_conflict_cong[rotated]) by auto
    from nc' disj' have ncx: "no_conflict (\<sigma>(x := x)) (foldr Local X c)"
      by (rule Cons.IH)

    have notin: "x \<notin> \<sigma> ` (fv (foldr Local X c) \<inter> var_subst_dom \<sigma>)"
      using disj image_iff by auto
    show ?case
      apply simp
      using ncx notin by (rule nc_Local)
  qed
qed

lemma no_conflict_fv:
  assumes "var_subst_dom \<sigma> \<inter> fv c = {}"
  shows "no_conflict \<sigma> c"
  by (metis Int_empty_right assms empty_is_image inf.commute localvars_dom_no_conflict)

lemma qrhlelimeq_aux:
  assumes "Q \<supseteq> fv c - overwr c"
  assumes "Q \<supseteq> fv d - overwr d"
  defines "Qtilde \<equiv> Q \<union> quantum' (fv c) \<union> quantum' (fv d)"
  defines "Qstar \<equiv> Qtilde - Q"
  shows "(Qstar \<inter> overwr c) \<union> (Qstar - fv c) = Qstar"
  and "(Qstar \<inter> overwr d) \<union> (Qstar - fv d) = Qstar"
  using assms by blast+

end

