section \<open>Commutative Idempotent Modulo\<close>

text \<open>Auxiliary theorem: A formalization of families of operations that are commutative and idempotent modulo an equivalent relation \<^term>\<open>R\<close>.\<close>

theory Comm_Idem_Modulo
  imports Main
begin

locale comm_idem_modulo =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes equiv_R: "equivp R"
  assumes cong_R: "R a b \<Longrightarrow> R (f x a) (f x b)"
  assumes f_idem: "R (f x (f x z)) (f x z)"
  assumes f_commute: "R (f y (f x z)) (f x (f y z))" begin

lemmas R_refl[simp] = equivp_reflp[OF equiv_R]
lemmas R_sym = equivp_symp[OF equiv_R]
lemmas R_trans[trans] = equivp_transp[OF equiv_R]

definition F :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b" where
  "F V C = (let V' = (SOME V'. set V' = V \<and> distinct V') in
    foldr f V' C)"

lemma F_empty[simp]: "F {} C = C"
  unfolding F_def apply auto
  by (metis (mono_tags, lifting) distinct.simps(1) foldr.simps(1) id_apply some_equality)

lemma F_singleton[simp]: "F {x} C = f x C"
proof -
  have "(SOME V'. set V' = {x} \<and> distinct V') = [x]"
    apply (rule someI2_ex)
    apply (metis List.set_insert distinct.simps(1) distinct_insert list.set(1))
    by (metis distinct.simps(2) distinct_length_2_or_more empty_set insert_not_empty list.exhaust singletonD)
  then show "F {x} C = f x C"
    unfolding F_def by simp
qed

lemma F_foldr: "R (F (set V) C) (foldr f V C)"
proof -
  define V' where "V' = (SOME V'. set V' = set V \<and> distinct V')"
  let ?eq = "\<lambda>V V'. R (foldr f V C) (foldr f V' C)"

  have eq: "R (F (set V) C) (foldr f V' C)"
    unfolding F_def V'_def by simp

  have induct[case_names 0 greater[pos IH]]: "P n"
    if "P 0" and "\<And>n. n >= 1 ==> (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n" for P and n :: nat
    apply (rule full_nat_induct) using that
    by (metis One_nat_def Suc_leI neq0_conv)

  have "set V = set V' \<and> distinct V'"
    unfolding V'_def apply (rule someI2_ex) 
    by (simp_all add: finite_distinct_list)
    
  then have "set V = set V'" and "distinct V'"
    by auto

  then have "R (foldr f V C) (foldr f V' C)"
  proof (induction "length V" arbitrary: V V' rule:induct)
    case 0
    then show ?case
      by simp
  next
    case greater
    from greater(1)
    obtain a V2 where V: "V = a # V2" and n: "length V2 <= length V"
      apply atomize_elim
      by (metis One_nat_def Suc_le_length_iff add.commute le_add2 list.size(4))

    consider (empty_V') "V' = []"
      | (V'_a) V'2 where "V' = a # V'2" and "a \<notin> set V2"
      | (V'_a2) V'2 where "V' = a # V'2" and "a \<in> set V2"
      | (V'_b) V'2 b where "V' = b # V'2" and "a \<noteq> b"
      apply atomize_elim
      by (metis list.exhaust)
    then show ?case
    proof cases
      case empty_V'
      then show ?thesis apply auto
        using greater.prems(1) V by auto
    next
      case V'_a
      with V greater
      have eq: "set V2 = set V'2" and dst: "distinct V'2"
        apply auto  
        using V'_a apply fastforce
        by (simp add: insert_ident)

      have "R (foldr f V2 C) (foldr f V'2 C)"
        apply (rule greater(2))
        using V eq dst by auto
      then show ?thesis
        unfolding V'_a V
        by (simp add: cong_R)
    next
      case V'_a2
      with greater V have eq: "set V2 = set (a # V'2)" and dst: "distinct (a # V'2)"
        by (auto simp add: insert_absorb)
      have "R (foldr f V2 C) (foldr f (a # V'2) C)"
        apply (rule greater)
        using V eq dst by auto
      then have "R (foldr f (a # V2) C) (foldr f (a # V') C)"
        unfolding V'_a2
        by (simp add: cong_R)
      also have "R \<dots> (foldr f V' C)"
        unfolding V'_a2 using f_idem by auto
      finally show ?thesis
        by (simp add: V)
    next
      case V'_b
      define V2b where "V2b = filter (\<lambda>x. x\<noteq>b) (remdups V2)"
      then have *: "set V2 = set (b # V2b)"
        using V V'_b(1) V'_b(2) greater.prems(1) by fastforce
      have len: "length (a # V2b) < length V"
      proof -
        have "length (a # V2b) = Suc (length V2b)"
          by simp
        also have "Suc (length V2b) \<le> length (remdups V2)"
          by (smt "*" V2b_def card_set distinct.simps(2) distinct_card distinct_filter distinct_remdups dual_order.order_iff_strict length_Cons mem_Collect_eq set_filter)
        also have "\<dots> \<le> length V2"
          by simp
        also have "\<dots> < length V"
          by (simp add: V)
        finally show ?thesis by -
      qed

      have "V = a # V2"
        by (simp add: V)
      also have "?eq V2 (b # V2b)"
        apply (rule greater)
        using V * V2b_def by auto
      then have "?eq (a # V2) (a # b # V2b)"
        by (simp add: cong_R)
      also have "?eq (a # b # V2b) (b # a # V2b)"
        using f_commute by simp
      also have *: "set (a # V2b) = set V'2"
        unfolding V2b_def apply auto
        using V V'_b(1) V'_b(2) greater.prems(1) apply auto[3]
        using V'_b(1) greater.prems(2) by auto
      have "?eq (a # V2b) V'2"
        apply (rule greater)
        using len * V'_b(1) greater.prems(2) by auto
      then have "?eq (b # a # V2b) (b # V'2)"
        by (simp add: cong_R)
      also have "b # V'2 = V'"
        by (simp add: V'_b(1))
      finally show ?thesis by -
    qed

  qed

  then show ?thesis
    using R_sym R_trans eq by blast
qed

lemma R_cong_F: 
  assumes "R C D"
  shows "R (F X C) (F X D)"
proof -
  define X' where "X' = (SOME X'. set X' = X \<and> distinct X')"
  have "R (foldr f X' C) (foldr f X' D)"
    apply (induction X')
    using assms cong_R by auto
  then show ?thesis
    by (simp add: F_def X'_def[symmetric] Let_def)
qed

lemma F_join:
  assumes "finite V" and "finite W"
  shows "R (F V (F W C)) (F (V\<union>W) C)"
proof -
  from assms
  obtain V' W' where V: "V = set V'" and W: "W = set W'"
    apply atomize_elim using finite_list by auto
  have "R (F W C) (foldr f W' C)"
    unfolding W
    by (simp add: F_foldr)
  then have "R (F V (F W C)) (F V (foldr f W' C))"
    using R_cong_F by blast
  also have "R \<dots> (foldr f V' (foldr f W' C))"
    by (simp add: V F_foldr)
  also have "\<dots> = foldr f (V'@W') C"
    by auto
  also have "R \<dots> (F (set (V'@W')) C)"
    using R_sym F_foldr by blast
  also have "set (V'@W') = V\<union>W"
    unfolding V W by simp
  finally show ?thesis
    by -
qed

lemma F_insert:
  assumes "finite Y"
  shows "R (F (insert x Y) C) (f x (F Y C))"
proof -
  have "F (insert x Y) C = F ({x} \<union> Y) C"
    by simp
  also have "R \<dots> (F {x} (F Y C))"
    apply (rule R_sym)
    apply (rule F_join)
    using assms by auto
  also have "\<dots> = f x (F Y C)"
    by simp
  finally show ?thesis
    by -
qed

lemma F_insert':
  assumes "finite Y"
  shows "R (F (insert x Y) C) (F Y (f x C))"
proof -
  have "F (insert x Y) C = F (Y \<union> {x}) C"
    by simp
  also have "R \<dots> (F Y (F {x} C))"
    apply (rule R_sym)
    apply (rule F_join)
    using assms by auto
  also have "\<dots> = F Y (f x C)"
    by simp
  finally show ?thesis
    by -
qed

lemma F_intro:
  assumes "finite X"
  assumes "\<And>X'. set X' = X \<Longrightarrow> distinct X' \<Longrightarrow> P (foldr f X')"
  shows "P (F X)"
    unfolding F_def Let_def
    apply (rule assms(2))
    apply (rule someI2_ex)
    apply (simp_all add: assms(1) finite_distinct_list)[2]
    apply (rule someI2_ex)
    by (simp_all add: assms(1) finite_distinct_list)[2]


lemma F_induct[consumes 1, case_names base step[IH X]]:
  assumes finite: "finite X"
  assumes base: "P {} C"
  assumes step: "\<And>D Y x. P Y D \<Longrightarrow> x\<in>X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> x \<notin> Y \<Longrightarrow> P (insert x Y) (f x D)"
  shows "P X (F X C)"
  using finite
proof (rule F_intro)
  fix X' :: "'a list"
  assume "distinct X'"
  assume "set X' = X"
  then have "set X' \<subseteq> X"
    by simp
  with \<open>distinct X'\<close> 
  have "P (set X') (foldr f X' C)"
  proof (induction X')
    case Nil
    from assms show ?case by simp
  next
    case (Cons a X')
    show ?case 
      apply simp
      apply (rule step)
      using Cons by auto
  qed
  then show "P X (foldr f X' C)"
    using \<open>set X' = X\<close> by blast
qed

lemma F_induct'[consumes 1, case_names base step[IH X]]:
  assumes finite: "finite X"
  assumes base: "P {} id"
  assumes step: "\<And>G Y x. P Y G \<Longrightarrow> x\<in>X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> x \<notin> Y \<Longrightarrow> P (insert x Y) (\<lambda>C. f x (G C))"
  shows "P X (F X)"
  using finite
proof (rule F_intro)
  fix X' :: "'a list"
  assume "distinct X'"
  assume "set X' = X"
  then have "set X' \<subseteq> X"
    by simp
  with \<open>distinct X'\<close> 
  have "P (set X') (foldr f X')"
  proof (induction X')
    case Nil
    from assms show ?case 
      by (auto simp: id_def)
  next
    case (Cons a X')
    show ?case 
      apply simp
      thm step
      apply (rule step)
      using Cons by auto
  qed
  then show "P X (foldr f X')"
    using \<open>set X' = X\<close> by blast
qed


end


end