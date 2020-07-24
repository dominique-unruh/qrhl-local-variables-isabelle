theory Locals_Up_Block
  imports Helping_Lemmas
begin


lemma locals_up_block:
  fixes Vup and Vstar and Vdown and V
    and c :: "nat \<Rightarrow> context" and n :: nat
  assumes [simp]: "finite Vup"
  defines "call \<equiv> block (map (\<lambda>i. locals (V i) (c i)) [0..<n])"
  defines "d \<equiv> (\<lambda>i. inits (Vstar i); locals (Vdown i) (c i))"
  defines "W \<equiv> rec_nat Vup (\<lambda>i W. W \<union> Vstar i - (fv (c i) - Vdown i))"
  assumes "\<And>i. i<n \<Longrightarrow> program (c i)"
  assumes "\<And>i. i<n \<Longrightarrow> finite (V i)"
  assumes "\<And>i. i<n \<Longrightarrow> Vstar i \<subseteq> Vup"
  assumes "\<And>i. i<n \<Longrightarrow> Vstar i \<supseteq> V i - Vdown i - W i"
  assumes "\<And>i. i<n \<Longrightarrow> Vdown i \<subseteq> V i"
  assumes "\<And>i. i<n \<Longrightarrow> V i \<subseteq> Vdown i \<union> Vup"
  assumes "fv call \<inter> Vup = {}"
  shows "call =d= locals Vup (block (map d [0..<n]))"
  using assms(2-) apply atomize
proof (induction n arbitrary: V Vdown c d Vstar W call)
  case 0
  then show ?case 
    using locals_unused[of Vup Skip] locals.R_sym by auto
next
  case (Suc n)

  have [simp]: "i < Suc n \<longleftrightarrow> i \<le> n" for i
    by auto

  from Suc.prems
  have d_def: "d i = inits (Vstar i) ; locals (Vdown i) (c i)"
    and W0: "W 0 = Vup"
    and W_Suc: "W (Suc i) = W i \<union> Vstar i - (fv (c i) - Vdown i)"
    and finite_V[simp]: "i\<le>n \<Longrightarrow> finite (V i)"
    and finite_c[simp]: "i\<le>n \<Longrightarrow> program (c i)"
    and fv_call: "fv call \<inter> Vup = {}"
    and VVW: "i<Suc n \<Longrightarrow> V i - Vdown i - W i \<subseteq> Vstar i"
    for i
    by auto

  have finite_Vstar[simp]: "i\<le>n \<Longrightarrow> finite (Vstar i)"
    and finite_Vdown[simp]: "i\<le>n \<Longrightarrow> finite (Vdown i)" for i
     apply (meson Suc.prems(6) assms(1) infinite_super le_trans lessI not_less)
    by (meson Suc.prems(8) finite_V finite_subset le_imp_less_Suc)

  define V' Vdown' Vstar' W' and c' d' c'all d'all
    where "V' i = V (Suc i)"
      and "Vdown' i = Vdown (Suc i)"
      and "Vstar' i = Vstar (Suc i)"
      and "W' = rec_nat Vup (\<lambda>i W. W \<union> Vstar' i - (fv (c' i) - Vdown' i))"
      and "c' i = c (Suc i)"
      and "d' i = d (Suc i)"
      and "c'all = block (map (\<lambda>i. locals (V' i) (c' i)) [0..<n])"
      and "d'all = block (map d' [0..<n])"
    for i

  have [simp]: "i \<le> n \<Longrightarrow> program (d i)" for i
    unfolding d_def
    by (simp add: program.intros(10) program_initsI program_localsI)
  have [simp]: "i < n \<Longrightarrow> program (d' i)" for i
    unfolding d'_def by auto 

  have [simp]: "program d'all"
    unfolding d'all_def apply (rule program_blockI)
    by auto
  have [simp]: "i\<le>Suc n \<Longrightarrow> finite (W i)" for i
    unfolding Suc apply (induction i) by auto

  have W'W: "W' i \<supseteq> W (Suc i)" for i
    apply (induction i)
    apply (simp add: Suc.prems W'_def W0 W_Suc sup.absorb1)
    using Vdown'_def Vstar'_def W'_def W_Suc c'_def by auto

  have VVdown': "V' i \<subseteq> Vdown' i \<union> Vup" if "i<n" for i
    by (simp add: Suc.prems Suc_leI V'_def Vdown'_def that)

  have VVW': "V' i - Vdown' i - W' i \<subseteq> Vstar' i" if "i<n" for i
    using that W'W VVW unfolding Vstar'_def V'_def Vdown'_def
    by (metis Diff_mono Suc_mono dual_order.trans subset_refl)

  have "call = locals (V 0) (c 0); c'all"
    unfolding Suc c'all_def
    apply (subst asm_rl[of "[0..<Suc n] = 0 # map Suc [0..<n]"])
     apply (simp add: map_Suc_upt upt_conv_Cons)
    by (simp add: o_def V'_def c'_def)
  with fv_call have fv_c'all: "fv c'all \<inter> Vup = {}"
    by auto

  note IH = Suc.IH[where V=V' and Vdown=Vdown' and Vstar=Vstar' and c=c' and d=d' and W=W' and call=c'all]
  
  have IH: "c'all =d=
   locals Vup (block (map d' [0..<n]))"
    apply (rule IH)
             apply (simp add: c'all_def)
            apply (simp add: Suc.prems Vstar'_def Vdown'_def d'_def c'_def)
           apply (simp add: W'_def)
          apply (simp add: Suc.prems c'_def)
         apply (simp add: Suc.prems V'_def)
        apply (simp add: Suc.prems Vstar'_def)
       apply (simp add: VVW')
      apply (simp add: Suc.prems V'_def Vdown'_def)
     apply (simp add: VVdown')
    by (simp add: fv_c'all)

  have "1 \<le> Suc n" by simp

  have "i \<le> n \<Longrightarrow> x \<notin> V i \<Longrightarrow> x \<in> fv (c i)
    \<Longrightarrow> x \<in> fv (c i) \<Longrightarrow> x \<in> fv call" for x i
    unfolding Suc apply auto by auto
  then have 1: "i \<le> n \<Longrightarrow> x \<notin> V i \<Longrightarrow> x \<in> fv (c i)
    \<Longrightarrow> x \<in> fv (c i) \<Longrightarrow> x \<notin> Vup" for x i
    using Suc by blast

  have *: "W i \<union>
    overwr (block (map d [i..<Suc n])) \<supseteq> Vup \<inter> fv (block (map d [i..<Suc n]))" 
    if "i \<le> Suc n" for i
    using that 
  proof (induction i rule:inc_induct)
    case base
    show ?case by simp
  next
    case (step i)
    define dSuc where "dSuc = block (map d [Suc i..<Suc n])"
    with step have [simp]: "i \<le> n" and 
      IH: "Vup \<inter> fv dSuc \<subseteq> (W i \<union> Vstar i - (fv (c i) - Vdown i)) 
            \<union> overwr dSuc"
      by (auto simp: W_Suc)
    have "Vup \<inter> fv (d i; dSuc) \<subseteq> W i \<union> overwr (d i; dSuc)"
      apply (auto simp: d_def)
            apply (metis "1" Diff_iff VVW \<open>i \<le> n\<close> step.hyps(2) subsetD)
            apply (metis "1" Diff_iff VVW \<open>i \<le> n\<close> step.hyps(2) subsetD)
          apply (simp add: Suc.prems(4) program_covered step.hyps(2))
      using IH apply auto[1]
        apply (metis "1" Diff_iff VVW \<open>i \<le> n\<close> step.hyps(2) subsetD)
       apply (simp add: Suc.prems(4) program_covered step.hyps(2))
      using IH by auto
    then show ?case
      unfolding dSuc_def
      by (metis block.simps(2) list.simps(9) step.hyps(2) upt_conv_Cons)
  qed
  have all_inits_removed: "((Vup-W 1)\<inter>fv d'all)-overwr d'all = {}"
    unfolding d'all_def d'_def 
    apply (insert *[OF \<open>1\<le>Suc n\<close>])
    apply (subst (asm) asm_rl[of "[1..<Suc n] = map Suc [0..<n]"],
           simp add: map_Suc_upt)
    apply (subst (asm) asm_rl[of "[1..<Suc n] = map Suc [0..<n]"],
           simp add: map_Suc_upt)
    by (auto simp add: o_def)
  have W1_fv_c0: "W 1 \<inter> fv (locals (Vdown 0) (c 0)) = {}"
    by (auto simp add: Suc)
  
  have "call
        =d=
        Seq (locals (V 0) (c 0)) (block (map (\<lambda>i. locals (V' i) (c' i)) [0..<n]))"
    unfolding Suc
    apply (subst asm_rl[of "[0..<Suc n] = 0 # (map Suc [0..<n])"])
     apply (simp add: map_Suc_upt upt_conv_Cons)
    by (simp add: o_def V'_def[symmetric] c'_def[symmetric])
  also have "\<dots> =d= locals (V 0) (c 0);
                    locals Vup d'all"
    unfolding d'all_def
    apply (rule denot_eq_seq_cong2)
    by (rule IH[unfolded c'all_def])
  also have "\<dots> =d= locals Vup (locals (V 0) (c 0));
                    locals Vup d'all"
    apply (rule denot_eq_seq_cong1)
    apply (rule locals_unused[THEN denot_eq'_sym])
    using 1 by auto
  also have "\<dots> =d= locals Vup (locals (Vdown 0) (c 0)); 
                    locals Vup d'all"
    apply (subgoal_tac "Vup \<union> Vdown 0 = Vup \<union> V 0")
    apply (smt \<open>program d'all\<close> assms(1) denot_eq_seq_cong1 finite_V finite_Vdown finite_c le0 locals.F_join locals.R_sym locals.R_trans program_localsI)
    using Suc by (smt Diff_partition Un_Diff_cancel W0 boolean_algebra_cancel.sup2 sup_commute zero_less_Suc)
  also have "\<dots> =d= locals Vup (locals (Vdown 0) (c 0);
                      inits Vup; d'all)"
    by (rule locals_seq_merge, auto)
  also have "\<dots> =d= locals Vup (locals (Vdown 0) (c 0);
                      (inits (W 1); inits (Vup-W 1)); d'all)"
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1)
    using inits_inits
    by (metis (no_types, lifting) Diff_Diff_Int Diff_cancel Diff_eq_empty_iff One_nat_def Suc.prems(6) Un_Diff_Int Un_Diff_cancel W0 W_Suc assms(1) finite_Un locals.R_sym zero_less_Suc)
  also have "\<dots> =d= locals Vup ((locals (Vdown 0) (c 0);
                      inits (W 1)); inits (Vup-W 1); d'all)"
    (* Associativity *)
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1)
    using denot_eq_seq_assoc locals.R_sym by blast
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      inits (Vup-W 1); d'all)"
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1)
    apply (rule swap)
    using W1_fv_c0 by auto
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      (inits ((Vup-W 1)\<inter>fv d'all); inits ((Vup-W 1)-fv d'all)); d'all)"
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1)
    by (metis Un_Diff_Int Un_commute assms(1) equivp_symp finite_Diff finite_Int inits_inits locals.equiv_R)
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      inits ((Vup-W 1)\<inter>fv d'all); (inits ((Vup-W 1)-fv d'all); d'all))"
    (* Associativity *)
    by (meson denot_eq'_trans denot_eq_cong_locals denot_eq_seq_assoc denot_eq_seq_cong1 locals.R_sym)
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      inits ((Vup-W 1)\<inter>fv d'all); d'all; 
                      inits ((Vup-W 1)-fv d'all))"
    (* Swapping inits ((Vup-W 1)-fv d'all); d'all *)
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1
        denot_eq'_trans[OF denot_eq_seq_assoc]
        denot_eq'_trans[OF _ denot_eq_seq_assoc[THEN denot_eq'_sym]])
    apply (rule swap)
    by auto
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      inits ((Vup-W 1)\<inter>fv d'all); d'all)"
    (* Removing "inits ((Vup-W 1)-fv d'all" at the end which only initializes
       local variables *)
    apply (rule locals_inits_end)
    by auto
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
          (inits (((Vup-W 1)\<inter>fv d'all)-overwr d'all); inits (((Vup-W 1)\<inter>fv d'all)\<inter>overwr d'all)); d'all)"
    (* Splitting inits ((Vup-W 1)\<inter>fv d'all) *)
    by (smt Diff_Diff_Int Diff_empty all_inits_removed denot_eq_cong_locals denot_eq_seq_cong1 denot_eq_seq_cong2 finite.emptyI locals.F_empty locals_inits_beginning)
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
          inits (((Vup-W 1)\<inter>fv d'all)-overwr d'all); (inits (((Vup-W 1)\<inter>fv d'all)\<inter>overwr d'all); d'all))"
    (* Associativity *)
    using denot_eq'_sym denot_eq_cong_locals denot_eq_seq_assoc denot_eq_seq_cong1 locals.R_trans by blast
  also have "\<dots> =d= locals Vup (inits (W 1); locals (Vdown 0) (c 0);
                      inits (((Vup-W 1)\<inter>fv d'all)-overwr d'all); d'all)"
    apply (intro denot_eq_cong_locals denot_eq_seq_cong2 denot_eq_seq_cong1)
    apply (rule inits_overwr)
    by simp
  also have "\<dots> =d= locals Vup (inits (W 1); (locals (Vdown 0) (c 0);
                      d'all))"
    unfolding all_inits_removed
    apply simp
    by (metis denot_eq_cong_locals denot_eq_seq_assoc denot_eq_seq_cong1 equivp_def locals.equiv_R seq_c_skip)
  also have "\<dots> =d= locals Vup (inits (Vstar 0); (locals (Vdown 0) (c 0);
                      d'all))"
    (* Replacing inits (W 0) by inits (Vstar 0), 
       possible because the difference is in Vup *)
    apply (rule locals_inits_change)
    apply auto[2]
    using Suc.prems W0 W_Suc by auto
  also have "\<dots> =d= locals Vup (d 0; d'all)"
    by (simp add: d_def denot_eq_cong_locals denot_eq_seq_assoc locals.R_sym)
  also have "\<dots> =d= locals Vup (block (map d [0..<Suc n]))"
    apply (subst asm_rl[of "[0..<Suc n] = 0 # (map Suc [0..<n])"])
     apply (simp add: map_Suc_upt upt_conv_Cons)
    unfolding d'all_def d'_def
    by (metis block.simps(2) locals.R_refl map_Suc_upt map_upt_Suc upt_conv_Cons zero_less_Suc)
  finally show ?case
    by -
qed

end
