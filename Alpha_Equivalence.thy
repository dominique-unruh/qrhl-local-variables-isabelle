section \<open>Alpha Equivalence\<close>

theory Alpha_Equivalence
  imports Helping_Lemmas
begin

inductive alpha_equivalent :: "context \<Rightarrow> context \<Rightarrow> bool" (infix "=a=" 50) where
  ae_Hole: "Hole i =a= Hole i"
| ae_Assign: "Assign X e =a= Assign X e"
| ae_Sample: "Sample Q e =a= Sample Q e"
| ae_Skip: "Skip =a= Skip"
| ae_QInit: "QInit Q e =a= QInit Q e"
| ae_QApply: "QApply Q e =a= QApply Q e"
| ae_Measure: "Measure X Q e =a= Measure X Q e"
| ae_IfTE: "p1 =a= p1' \<Longrightarrow> p2 =a= p2' \<Longrightarrow> IfTE e p1 p2 =a= IfTE e p1' p2'"
| ae_While: "p =a= p' \<Longrightarrow> While e p =a= While e p'"
| ae_Seq: "p1 =a= p1' \<Longrightarrow> p2 =a= p2' \<Longrightarrow> Seq p1 p2 =a= Seq p1' p2'"
| ae_Local: "compatible y z \<Longrightarrow> compatible x z \<Longrightarrow> z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow>
    z \<notin> vars p1 \<Longrightarrow> z \<notin> vars p2 \<Longrightarrow> 
    full_subst_vars (transpose x z) p1 =a= full_subst_vars (transpose y z) p2 \<Longrightarrow>
    Local x p1 =a= Local y p2"


inductive_cases alpha_eq_cases:
  "Local x c =a= d"
  "IfTE e c1 c2 =a= d"
  "While e c =a= d"
  "Seq c1 c2 =a= d"
  "Hole i =a= d"
  "Assign x e =a= d"
  "Sample x e =a= d"
  "Skip =a= d"
  "QApply Q e =a= d"
  "QInit Q e =a= d"
  "Measure X Q e =a= d"


lemma alpha_eq_sym[sym]:
  assumes "c =a= d"
  shows "d =a= c"
  using assms apply induction
  by (auto simp: alpha_equivalent.intros)

lemma fv_alpha:
  assumes "c =a= d"
  shows "fv c = fv d"
  using assms
proof induction
  case (ae_Local y z x p1 p2)
  then have "z \<notin> fv p1" and "z \<notin> fv p2"
    using fv_vars by auto
  note [simp] = \<open>compatible x z\<close> \<open>compatible y z\<close>
  have [simp]: "valid_var_subst (transpose x z)" if "compatible x z" for x z
    unfolding valid_var_subst_def
    using that valid_var_subst_def valid_var_subst_transpose by blast
  have [simp]: "inj_on (transpose x z) X" for x :: 'z and z X
    by simp
  from ae_Local.IH
  have "transpose x z ` fv p1 = transpose y z ` fv p2"
    by (subst (asm) fv_full_subst_vars; simp)+
  with \<open>z \<notin> fv p1\<close> \<open>z \<notin> fv p2\<close>
  have "fv p1 - {x} = fv p2 - {y}"
    apply auto
       apply (metis in_transpose_image_iff transpose_apply_other transpose_def)
      apply (metis imageI in_transpose_image_iff transpose_eq_iff)
     apply (metis in_transpose_image_iff transpose_def)
    by (metis in_transpose_image_iff transpose_eq_iff)
  then show ?case
    by simp
qed auto


lemma alpha_eq_refl[simp]: \<open>c =a= c\<close>
proof (induction c rule:measure_induct_rule[of size])
  case (less c)
  show "c =a= c"
  proof (cases c)
    case (While e c')
    show ?thesis
      unfolding While
      apply (rule alpha_equivalent.intros)
      apply (rule less)
      using While by simp
  next
    case (IfTE e c1 c2)
    show ?thesis
      unfolding IfTE
      apply (rule alpha_equivalent.intros; rule less)
      using IfTE by simp_all
  next
    case (Seq c1 c2)
    show ?thesis
      unfolding Seq
      apply (rule alpha_equivalent.intros; rule less)
      using Seq by simp_all
  next
    case (Local x c)
    from finite_vars
    obtain z where "compatible x z" and "x \<noteq> z" and "z \<notin> vars c"
      apply atomize_elim
      apply (rule fresh_compatible)
      by simp
  then show ?thesis
    unfolding Local
    apply (rule_tac ae_Local, auto)
    apply (rule less)
    unfolding Local
    by auto
  qed (auto intro: alpha_equivalent.intros)
qed


lemma alpha_eq_full_subst:
  assumes valid: "valid_var_subst f" and inj: "inj f"
  assumes "c =a= d"
  shows "full_subst_vars f c =a= full_subst_vars f d"
  using assms(3)
proof (induction)
  case (ae_Local y z x p1 p2)
  have "full_subst_vars (transpose (f x) (f z)) (full_subst_vars f p1)
        = full_subst_vars (transpose (f x) (f z) \<circ> f) p1"
    using valid by (rule full_subst_vars_compose)
  also have "transpose (f x) (f z) \<circ> f = f \<circ> transpose x z"
    unfolding transpose_def o_def
    using inj inj_eq by fastforce
  also have "full_subst_vars (f \<circ> transpose x z) p1 
           = full_subst_vars f (full_subst_vars (transpose x z) p1)"
    apply (rule full_subst_vars_compose[symmetric])
    by (simp add: ae_Local.hyps(2))
  also have "\<dots> =a= full_subst_vars f (full_subst_vars (transpose y z) p2)"
    by (rule ae_Local.IH)
  thm ae_Local.IH
  also have "\<dots> = full_subst_vars (f \<circ> transpose y z) p2"
    apply (rule full_subst_vars_compose)
    by (simp add: ae_Local.hyps(1))
  also have "f \<circ> transpose y z = transpose (f y) (f z) \<circ> f"
    unfolding transpose_def o_def
    using inj inj_eq by fastforce
  also have "full_subst_vars (transpose (f y) (f z) \<circ> f) p2
           = full_subst_vars (transpose (f y) (f z)) (full_subst_vars f p2)"
    using valid by (rule full_subst_vars_compose[symmetric])
  finally 
  have *: "full_subst_vars (transpose (f x) (f z)) (full_subst_vars f p1) =a=
    full_subst_vars (transpose (f y) (f z)) (full_subst_vars f p2)"
    by -

  show ?case
    apply simp
    apply (rule alpha_equivalent.ae_Local[where z="f z"])
    using valid ae_Local.hyps(1) ae_Local.prems compatible_sym compatible_trans valid_var_subst_def apply blast
    using valid ae_Local.hyps(2) ae_Local.prems compatible_sym compatible_trans valid_var_subst_def apply blast
    apply (simp add: ae_Local.hyps(3) inj inj_eq)
    apply (simp add: ae_Local.hyps(4) inj inj_eq)
    apply (simp add: ae_Local.hyps(5) inj inj_image_mem_iff valid vars_full_subst_vars)
    apply (simp add: ae_Local.hyps(6) inj inj_image_mem_iff valid vars_full_subst_vars)
    using * by -
qed (auto simp: ae_IfTE ae_While ae_Seq)


lemma alpha_rename_fresh:
  assumes "finite avoid"
  shows "\<exists>c'. c =a= c' \<and> localvars c' \<inter> avoid = {}"
  using \<open>finite avoid\<close>
proof (induction c arbitrary: avoid)
  case (Hole i)
  show ?case 
    apply (rule exI[of _ "Hole i"])
    by auto
next
  case (Assign x e)
  show ?case 
    apply (rule exI[of _ "Assign x e"])
    by auto
next
  case (Sample x e)
  show ?case 
    apply (rule exI[of _ "Sample x e"])
    by auto
next
  case Skip
  show ?case 
    apply (rule exI[of _ "Skip"])
    by auto
next
  case (QInit Q e)
  show ?case 
    apply (rule exI[of _ "QInit Q e"])
    by auto
next
  case (QApply Q e)
  show ?case 
    apply (rule exI[of _ "QApply Q e"])
    by auto
next
  case (Measure X Q e)
  show ?case 
    apply (rule exI[of _ "Measure X Q e"])
    by auto
next
  case (IfTE e c1 c2)
  then obtain c1' c2' where "c1 =a= c1' \<and> localvars c1' \<inter> avoid = {}"
    and "c2 =a= c2' \<and> localvars c2' \<inter> avoid = {}"
    by metis
  then show ?case 
    apply (rule_tac exI[of _ "IfTE e c1' c2'"])
    by (auto intro: alpha_equivalent.intros)
next
  case (Seq c1 c2)
  then obtain c1' c2' where "c1 =a= c1' \<and> localvars c1' \<inter> avoid = {}"
    and "c2 =a= c2' \<and> localvars c2' \<inter> avoid = {}"
    by metis
  then show ?case 
    apply (rule_tac exI[of _ "Seq c1' c2'"])
    by (auto intro: alpha_equivalent.intros)
next
  case (While e c)
  then obtain c' where "c =a= c' \<and> localvars c' \<inter> avoid = {}"
    by metis
  then show ?case 
    apply (rule_tac exI[of _ "While e c'"])
    by (auto intro: alpha_equivalent.intros)
next
  case (Local x c)
  obtain c' where cc': "c =a= c'" and c'_avoid: "localvars c' \<inter> (insert x avoid) = {}"
    apply atomize_elim apply (rule Local.IH)
    using Local.prems by simp
  obtain y where "compatible x y" and "x \<noteq> y" and "y \<notin> vars c" and "y \<notin> vars c'" 
    and "y \<notin> avoid"
    using Local.prems by (atomize_elim, rule_tac fresh_compatible, simp)
  obtain z where "compatible x z" and "z \<noteq> x" and "z \<noteq> y" and "z \<notin> vars c" and "z \<notin> localvars c'"
    and "z \<notin> avoid"
    using Local.prems by (atomize_elim, rule_tac fresh_compatible, simp)
  have "compatible y z"
    using \<open>compatible x y\<close> \<open>compatible x z\<close> compatible_sym compatible_trans by blast
  define c'' where "c'' = full_subst_vars (transpose y z o transpose x z) c'"

  have valid_swap_comp: "valid_var_subst (transpose y z \<circ> transpose x z)"
    unfolding valid_var_subst_def apply auto
  by (metis \<open>compatible x y\<close> \<open>compatible x z\<close> \<open>compatible y z\<close> compatible_refl compatible_sym transpose_apply_second transpose_def)

  have cc'': "full_subst_vars (transpose x z) c =a= full_subst_vars (transpose y z) c''"
    unfolding c''_def
    apply (subst full_subst_vars_compose, fact valid_swap_comp)
    apply (simp add: flip: comp_assoc)
    using _ _ cc' apply (rule alpha_eq_full_subst)
    by (simp_all add: \<open>compatible x z\<close>)

  have "(transpose y z \<circ> transpose x z) ((transpose x z \<circ> transpose y z) z) \<notin> vars c''"
    unfolding c''_def 
    apply (subst vars_full_subst_vars[OF valid_swap_comp])
    apply (subst inj_image_mem_iff)
     apply (simp add: inj_compose)
    using \<open>x \<noteq> y\<close> \<open>y \<notin> vars c'\<close> \<open>z \<noteq> y\<close> by auto
  then have "z \<notin> vars c''"
    by simp

  have c''avoid: "localvars c'' \<inter> avoid = {}"
  proof auto
    fix v assume "v \<in> localvars c''" and "v \<in> avoid"
    then have "v \<in> (transpose y z o transpose x z) ` localvars c'"
      unfolding c''_def by simp
    then have vc': "(transpose x z o transpose y z) v \<in> localvars c'"
      by auto
    from \<open>v \<in> avoid\<close> \<open>z \<notin> avoid\<close> \<open>y \<notin> avoid\<close> have "v \<noteq> z" and "v \<noteq> y"
      by auto
    from vc' \<open>x\<noteq>y\<close> \<open>v\<noteq>z\<close> \<open>z \<notin> localvars c'\<close>
    have "v \<noteq> x"
      by auto
    with vc' \<open>v\<noteq>y\<close> \<open>v\<noteq>z\<close> have "v \<in> localvars c'"
      by auto
    then show False
      using c'_avoid \<open>v \<in> avoid\<close> by blast
  qed

  show ?case
    apply (rule_tac exI[of _ "Local y c''"])
    using cc'' \<open>compatible x z\<close> \<open>compatible y z\<close> \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> \<open>z \<notin> vars c\<close> \<open>y \<notin> avoid\<close>
      \<open>z \<notin> vars c''\<close> c''avoid
    by (auto intro!: ae_Local[where z=z])
qed

lemma ae_Local_arbitrary_z:
  assumes ae: "Local x c =a= Local y d"
  assumes "compatible y z"
    and "compatible x z"
    and "z \<noteq> x"
    and "z \<noteq> y"
    and "z \<notin> vars c"
    and "z \<notin> vars d"
  shows "full_subst_vars (transpose x z) c =a=
         full_subst_vars (transpose y z) d"
proof -
  from ae 
  obtain z' where [simp]: "compatible y z'"
    and [simp]: "compatible x z'"
    and "z' \<noteq> x"
    and "z' \<noteq> y"
    and "z' \<notin> vars c"
    and "z' \<notin> vars d"
    and ae': "full_subst_vars (transpose x z') c =a=
              full_subst_vars (transpose y z') d"
    apply (rule alpha_eq_cases)
    by auto

  have [simp]: "valid_var_subst (transpose z z')"
               "valid_var_subst (transpose x z')"
               "valid_var_subst (transpose y z')"
               "valid_var_subst (transpose x z)"
               "valid_var_subst (transpose y z)"
    apply (simp_all add: assms)
    using \<open>compatible y z'\<close> assms(2) compatible_sym compatible_trans valid_var_subst_transpose by blast

  have "full_subst_vars (transpose z z') (full_subst_vars (transpose x z') c) =a=
        full_subst_vars (transpose z z') (full_subst_vars (transpose y z') d)"
    using _ _ ae' apply (rule alpha_eq_full_subst)
    by auto

  then have *: "full_subst_vars (transpose z z' \<circ> transpose x z') c =a=
                full_subst_vars (transpose z z' \<circ> transpose y z') d"
    apply (subst full_subst_vars_compose[symmetric], simp)
    apply (subst full_subst_vars_compose[symmetric], simp)
    by -

  have 1: "(transpose z z' \<circ> transpose x z') v = transpose x z v"
    if "v \<in> vars c" for v
  proof -
    have "v \<noteq> z'"
      using \<open>z' \<notin> vars c\<close> that by blast
    have "v \<noteq> z"
      using assms(6) that by blast
    show ?thesis
      apply (cases "v=x")
      using \<open>v \<noteq> z\<close> \<open>v \<noteq> z'\<close> by auto
  qed

  have 2: "(transpose z z' \<circ> transpose y z') v = transpose y z v"
    if "v \<in> vars d" for v
  proof -
    have "v \<noteq> z'"
      using \<open>z' \<notin> vars d\<close> that by blast
    have "v \<noteq> z"
      using assms(7) that by blast
    show ?thesis
      apply (cases "v=y")
      using \<open>v \<noteq> z\<close> \<open>v \<noteq> z'\<close> by auto
  qed

  from *
  show "full_subst_vars (transpose x z) c =a=
        full_subst_vars (transpose y z) d"
    apply (subst full_subst_vars_cong, simp)
     apply (rule 1[symmetric], simp)
    apply (subst (2) full_subst_vars_cong, simp)
     apply (rule 2[symmetric], simp)
    by assumption
qed



lemma alpha_eq_trans[trans]:
  assumes "c =a= d" and "d =a= e"
  shows "c =a= e"
  using assms
proof (induction c arbitrary: d e rule:measure_induct_rule[of size])
  case (less c' d' e')
  show ?case
  proof (cases c')
    case (Local x c)
    note c'_def = this

    obtain d y where d'_def: "d' = Local y d" and [simp]: "compatible x y"
      using \<open>c' =a= d'\<close> unfolding c'_def apply (rule alpha_eq_cases)
      using compatible_sym compatible_trans by blast

    obtain e w where e'_def: "e' = Local w e" and [simp]: "compatible y w"
      using \<open>d' =a= e'\<close> unfolding d'_def apply (rule alpha_eq_cases)
      using compatible_sym compatible_trans by blast

    obtain z where [simp]: "compatible x z" and [simp]: "z \<noteq> x" and [simp]: "z \<noteq> y" and [simp]: "z \<noteq> w" 
      and [simp]: "z \<notin> vars c" and [simp]: "z \<notin> vars d" and [simp]: "z \<notin> vars e"
      apply atomize_elim
      apply (rule fresh_compatible)
      by simp

    have [simp]: "compatible y z"
      using \<open>compatible x y\<close> \<open>compatible x z\<close> compatible_sym compatible_trans by blast
    have [simp]: "compatible w z"
      using \<open>compatible y w\<close> \<open>compatible y z\<close> compatible_sym compatible_trans by blast

    have "full_subst_vars (transpose x z) c =a= full_subst_vars (transpose y z) d"
      apply (rule ae_Local_arbitrary_z)
      using \<open>c' =a= d'\<close> by (simp_all add: c'_def d'_def)

    moreover have "full_subst_vars (transpose y z) d =a= full_subst_vars (transpose w z) e"
      apply (rule ae_Local_arbitrary_z)
      using \<open>d' =a= e'\<close> by (simp_all add: d'_def e'_def)

    ultimately have "full_subst_vars (transpose x z) c =a= \<dots>"
      apply (rule less.IH[rotated])
      unfolding c'_def by simp

    then show ?thesis
      unfolding c'_def e'_def
      apply (rule ae_Local[rotated -1])
      by auto
  qed (use less in \<open>auto intro: alpha_equivalent.intros elim!: alpha_eq_cases\<close>)
qed



lemma subst_vars_alpha_eq:
  assumes "c =a= d"
  assumes "no_conflict \<sigma> c"
  assumes "no_conflict \<sigma> d"
  assumes "valid_var_subst \<sigma>"
  shows "subst_vars \<sigma> c =a= subst_vars \<sigma> d"
  using assms 
proof (induction c arbitrary: d \<sigma> rule:measure_induct_rule[of size])
  case (less c)
  define \<sigma>' where "\<sigma>' x = (if x \<in> fv c \<union> fv d then \<sigma> x else x)" for x
  have [simp]: "no_conflict \<sigma>' c" "no_conflict \<sigma>' d" "valid_var_subst \<sigma>'"
    using less \<sigma>'_def apply (simp add: no_conflict_cong)
    using less \<sigma>'_def apply (simp add: no_conflict_cong)
    using \<sigma>'_def less.prems(4) valid_var_subst_def by auto
  have "subst_vars \<sigma>' c =a= subst_vars \<sigma>' d"
  proof (cases c)
    case (Local x c')
    note c_def = Local
    from \<open>c =a= d\<close> obtain y d' z where d_def: "d = Local y d'" and [simp]:"compatible y z"
      and [simp]:"compatible x z" and "z \<noteq> x" and "z \<noteq> y" and "z \<notin> vars c'" and "z \<notin> vars d'"
      and "full_subst_vars (transpose x z) c' =a= full_subst_vars (transpose y z) d'"
      unfolding Local apply -
      apply (drule alpha_eq_cases)
      by auto

    have [simp]: "valid_var_subst (transpose x z)"
      by (simp add: compatible_sym transpose_def valid_var_subst_def)
    have [simp]: "valid_var_subst (transpose y z)"
      by (simp add: compatible_sym transpose_def valid_var_subst_def)
    have [simp]: "inj_on (transpose x z) A" for x z :: 'z and A
      by simp

    obtain z' where [simp]: \<open>compatible y z'\<close> \<open>z' \<noteq> x\<close> \<open>z' \<noteq> y\<close>
      \<open>z' \<notin> vars c'\<close> \<open>z' \<notin> vars d'\<close>
      \<open>z' \<notin> \<sigma> ` fv c'\<close> \<open>z' \<notin> \<sigma> ` fv d'\<close>
      apply atomize_elim
      apply (rule fresh_compatible)
      by simp
    moreover have [simp]: "compatible x z'"
      using \<open>compatible x z\<close> \<open>compatible y z\<close> calculation(1) compatible_sym compatible_trans by blast
    ultimately 
    have ae': "full_subst_vars (transpose x z') c' =a=
             full_subst_vars (transpose y z') d'"
      using \<open>c =a= d\<close> unfolding c_def d_def
      apply (rule_tac ae_Local_arbitrary_z[where z=z'])
      by auto

    have [simp]: "valid_var_subst (transpose x z')"
      by simp
    have [simp]: "valid_var_subst (transpose y z')"
      by simp
    have [simp]: "valid_var_subst (transpose z z')"
      by (metis \<open>compatible y z\<close> \<open>valid_var_subst (Transposition.transpose y z')\<close> compatible_trans transpose_apply_second valid_var_subst_def valid_var_subst_transpose)

    have [simp]: "transpose x y z = x \<longleftrightarrow> z = y" for x y z :: 'z
      by (metis transpose_eq_iff)
    have [simp]: "transpose x y z = y \<longleftrightarrow> z = x" for x y z :: 'z
      by (metis transpose_eq_iff)

    from \<open>no_conflict \<sigma>' c\<close>
    have nc_\<sigma>x_c': \<open>no_conflict (\<sigma>'(x := x)) c'\<close>
      unfolding c_def by (rule ic_nc_Local)
    from \<open>no_conflict \<sigma>' d\<close>
    have nc_\<sigma>x_d': \<open>no_conflict (\<sigma>'(y := y)) d'\<close>
      unfolding d_def by (rule ic_nc_Local)

    note \<open>z \<notin> vars c'\<close> \<open>z \<notin> vars d'\<close>
    note \<open>no_conflict \<sigma>' c\<close> 
    then have "no_conflict (\<sigma>'(x:=x)) c'" and "x \<notin> \<sigma>' ` (fv c' \<inter> var_subst_dom \<sigma>')"
      unfolding c_def
      by (rule ic_nc_Local, simp)+
    note \<open>no_conflict \<sigma>' d\<close> 
    then have "no_conflict (\<sigma>'(y:=y)) d'" and "y \<notin> \<sigma>' ` (fv d' \<inter> var_subst_dom \<sigma>')"
      unfolding d_def
      by (rule ic_nc_Local, simp)+
    note \<open>no_conflict \<sigma>' c\<close>
    note \<open>full_subst_vars (transpose x z) c' =a= 
        full_subst_vars (transpose y z) d'\<close>

    have [simp]: \<open>z' \<notin> fv c'\<close>
      using \<open>z' \<notin> vars c'\<close> fv_vars by blast
    have [simp]: \<open>z' \<notin> fv d'\<close>
      using \<open>z' \<notin> vars d'\<close> fv_vars by blast

    have eq_subst1: "(transpose x z' \<circ> \<sigma>'(x := x) \<circ> inv (transpose x z')) v = 
        (\<sigma>'(z':=z')) v" if "v \<in> fv (full_subst_vars (transpose x z') c')" for v
      using that apply (auto simp: fv_full_subst_vars)
      apply (subgoal_tac "\<And>v. v \<in> fv c' \<Longrightarrow> v \<noteq> x \<Longrightarrow> \<sigma>' v \<noteq> x")
       apply (metis \<open>z' \<notin> \<sigma> ` fv c'\<close> \<open>z' \<notin> fv c'\<close> \<sigma>'_def rev_image_eqI transpose_def)
      using \<open>x \<notin> \<sigma>' ` (fv c' \<inter> var_subst_dom \<sigma>')\<close> var_subst_dom_def by fastforce

    have eq_subst2: "(transpose y z' \<circ> \<sigma>'(y := y) \<circ> inv (transpose y z')) v = 
        (\<sigma>'(z':=z')) v" if "v \<in> fv (full_subst_vars (transpose y z') d')" for v
      using that apply (auto simp: fv_full_subst_vars)
      apply (subgoal_tac "\<And>v. v \<in> fv d' \<Longrightarrow> v \<noteq> y \<Longrightarrow> \<sigma>' v \<noteq> y")
       apply (metis \<open>z' \<notin> \<sigma> ` fv d'\<close> \<open>z' \<notin> fv d'\<close> \<sigma>'_def rev_image_eqI transpose_def)
      using \<open>y \<notin> \<sigma>' ` (fv d' \<inter> var_subst_dom \<sigma>')\<close> var_subst_dom_def by fastforce

    have nc1: "no_conflict (\<sigma>'(z' := z')) (full_subst_vars (transpose x z') c')"
      using eq_subst1 apply (rule no_conflict_cong, simp)
      apply (rule no_conflict_full_subst_vars, simp, simp)
      using \<open>no_conflict (\<sigma>'(x := x)) c'\<close> by blast
    have nc2: "no_conflict (\<sigma>'(z' := z')) (full_subst_vars (transpose y z') d')"
      using eq_subst2 apply (rule no_conflict_cong, simp)
      apply (rule no_conflict_full_subst_vars, simp, simp)
      using \<open>no_conflict (\<sigma>'(y := y)) d'\<close> by blast

    have "full_subst_vars (transpose x z') (subst_vars (\<sigma>'(x := x)) c') =a=
        full_subst_vars (transpose y z') (subst_vars (\<sigma>'(y := y)) d')"
      apply (subst full_subst_vars_subst_vars_comm)
         apply auto[3]
      apply (subst full_subst_vars_subst_vars_comm)
         apply auto[3]
      apply (subst subst_vars_cong[OF _ eq_subst1])
        apply (simp_all add: valid_var_subst_comp)[2]
      apply (subst subst_vars_cong[OF _ eq_subst2])
        apply (simp_all add: valid_var_subst_comp)[2]
      apply (rule less.IH)
          apply (auto simp: c_def)[1]
      using ae' nc1 nc2 \<open>valid_var_subst \<sigma>'\<close> subst_vars_rm_valid by blast+
    then show ?thesis
      apply (simp add: c_def d_def)
      apply (rule alpha_equivalent.ae_Local[where z=z'], auto)
       apply (simp add: vars_fv_localvars fv_subst_vars' nc_\<sigma>x_c')
      using \<sigma>'_def \<open>z' \<notin> \<sigma> ` fv c'\<close> \<open>z' \<notin> vars c'\<close> vars_fv_localvars apply fastforce
      apply (simp add: vars_fv_localvars fv_subst_vars' nc_\<sigma>x_d')
      using \<sigma>'_def \<open>z' \<notin> \<sigma> ` fv d'\<close> \<open>z' \<notin> vars d'\<close> vars_fv_localvars by fastforce
  next
    case (IfTE e c1 c2)
    note c_def = this
    from \<open>c =a= d\<close> obtain d1 d2 where d_def: "d = IfTE e d1 d2" and "c1 =a= d1" and "c2 =a= d2"
      unfolding c_def apply -
      apply (drule alpha_eq_cases)
      by auto
    have "subst_vars \<sigma>' c1 =a= subst_vars \<sigma>' d1"
      apply (rule less.IH)
      unfolding c_def apply auto
      apply (simp add: \<open>c1 =a= d1\<close>)
      using \<open>no_conflict \<sigma>' c\<close> c_def ic_nc_IfTE apply blast
      using \<open>no_conflict \<sigma>' d\<close> d_def ic_nc_IfTE by blast
    moreover have "subst_vars \<sigma>' c2 =a= subst_vars \<sigma>' d2"
      apply (rule less.IH)
      unfolding c_def apply auto
      apply (simp add: \<open>c2 =a= d2\<close>)
      using \<open>no_conflict \<sigma>' c\<close> c_def ic_nc_IfTE apply blast
      using \<open>no_conflict \<sigma>' d\<close> d_def ic_nc_IfTE by blast
    ultimately show ?thesis
      unfolding c_def d_def
      by (auto simp: ae_IfTE)
  next
    case (While e c1)
    note c_def = this
    from \<open>c =a= d\<close> obtain d1 where d_def: "d = While e d1" and "c1 =a= d1"
      unfolding c_def apply -
      apply (drule alpha_eq_cases)
      by auto
    have "subst_vars \<sigma>' c1 =a= subst_vars \<sigma>' d1"
      apply (rule less.IH)
      unfolding c_def apply auto
      apply (simp add: \<open>c1 =a= d1\<close>)
      using \<open>no_conflict \<sigma>' c\<close> c_def ic_nc_While apply blast
      using \<open>no_conflict \<sigma>' d\<close> d_def ic_nc_While by blast
    then show ?thesis
      unfolding c_def d_def
      by (auto simp: ae_While)
  next
    case (Seq c1 c2)
    note c_def = this
    from \<open>c =a= d\<close> obtain d1 d2 where d_def: "d = Seq d1 d2"
      and "c1 =a= d1" and "c2 =a= d2"
      unfolding c_def apply -
      apply (drule alpha_eq_cases)
      by auto
    have "subst_vars \<sigma>' c1 =a= subst_vars \<sigma>' d1"
      apply (rule less.IH)
      unfolding c_def apply auto
      apply (simp add: \<open>c1 =a= d1\<close>)
      using \<open>no_conflict \<sigma>' c\<close> c_def ic_nc_Seq apply blast
      using \<open>no_conflict \<sigma>' d\<close> d_def ic_nc_Seq by blast
    moreover have "subst_vars \<sigma>' c2 =a= subst_vars \<sigma>' d2"
      apply (rule less.IH)
      unfolding c_def apply auto
      apply (simp add: \<open>c2 =a= d2\<close>)
      using \<open>no_conflict \<sigma>' c\<close> c_def ic_nc_Seq apply blast
      using \<open>no_conflict \<sigma>' d\<close> d_def ic_nc_Seq by blast
    ultimately show ?thesis
      unfolding c_def d_def
      by (auto simp: ae_Seq)
  qed (insert \<open>c =a= d\<close>, auto elim: alpha_eq_cases)

  then show ?case
    apply (subst subst_vars_cong[where \<tau>=\<sigma>'])
    using less.prems apply (auto simp: \<sigma>'_def)[2]
    apply (subst subst_vars_cong[where \<sigma>=\<sigma> and \<tau>=\<sigma>'])
    using less.prems apply (auto simp: \<sigma>'_def)[2]
    by -
qed


lemma alpha_Local_cong[intro]: 
  assumes "c =a= d"
  shows "Local x c =a= Local x d"
proof -
  obtain z where [simp]: "compatible x z" and [simp]: "z \<noteq> x"
    and [simp]: "z \<notin> vars c" and [simp]: "z \<notin> vars d" 
    apply atomize_elim
    apply (rule fresh_compatible)
    by simp

  from \<open>c =a= d\<close>
  have "full_subst_vars (transpose x z) c =a= full_subst_vars (transpose x z) d"
    apply (rule alpha_eq_full_subst[rotated -1])
    by auto
  then show ?thesis
    apply (rule ae_Local[rotated -1])
    by simp_all
qed

lemma alpha_foldr_Local_cong[intro]: 
  assumes "c =a= d"
  shows "foldr Local V c =a= foldr Local V d"
  using assms by (induction V, auto)


lemma alpha_eq_local_unused:
  assumes "x \<notin> fv c" and "y \<notin> fv c" and "compatible x y"
  shows "Local x c =a= Local y c"
proof -
  obtain c' where "c =a= c'" and "localvars c' \<inter> (fv c \<union> {x,y}) = {}"
    apply (atomize_elim, rule alpha_rename_fresh)
    by simp

  obtain z where [simp]: "compatible x z" and [simp]: "z \<notin> vars c'" 
    and [simp]: "z \<noteq> x" and [simp]: "z \<noteq> y"
    apply (atomize_elim, rule fresh_compatible)
    by simp

  have [simp]: "compatible y z"
    using \<open>compatible x z\<close> assms(3) compatible_sym compatible_trans by blast

  have "x \<notin> vars c'"
    using \<open>c =a= c'\<close> \<open>localvars c' \<inter> (fv c \<union> {x, y}) = {}\<close> assms(1) fv_alpha vars_fv_localvars by auto 
  with \<open>z \<notin> vars c'\<close> have 1: "full_subst_vars (transpose x z) c' = c'"
    by (smt \<open>compatible x z\<close> full_subst_vars_cong full_subst_vars_id' id_apply transpose_def valid_var_subst_transpose)

  have "y \<notin> vars c'"
    using \<open>c =a= c'\<close> \<open>localvars c' \<inter> (fv c \<union> {x, y}) = {}\<close> assms(2) fv_alpha vars_fv_localvars by auto
  with \<open>z \<notin> vars c'\<close> have 2: "full_subst_vars (transpose y z) c' = c'"
    by (smt (z3) "1" \<open>compatible y z\<close> \<open>x \<notin> vars c'\<close> full_subst_vars_cong transpose_apply_other valid_var_subst_transpose)

  have "full_subst_vars (transpose x z) c' =a= full_subst_vars (transpose y z) c'"
    unfolding 1 2 by simp

  then have "Local x c' =a= Local y c'"
    apply (rule ae_Local[rotated -1])
    by simp_all

  with \<open>c =a= c'\<close> show "Local x c =a= Local y c"
    by (meson alpha_Local_cong alpha_eq_sym alpha_eq_trans)
qed

lemma rename_locals_alpha:
  fixes \<sigma> V
  defines "W \<equiv> map \<sigma> V"
  assumes valid: "valid_var_subst \<sigma>"
  assumes inj: "inj_on \<sigma> (set V)"
  assumes disj: "(fv c - set V) \<inter> set W = {}"
  assumes dom: "var_subst_dom \<sigma> \<subseteq> set V"
  assumes no: "no_conflict \<sigma> c"
  shows "foldr Local V c =a= foldr Local W (subst_vars \<sigma> c)"
  using assms(2-) unfolding W_def 
proof (induction V arbitrary: \<sigma> c)
  case Nil
  from \<open>var_subst_dom \<sigma> \<subseteq> set []\<close> have "\<sigma> = id"
    by (metis (mono_tags) empty_iff empty_set empty_subsetI eq_id_iff mem_Collect_eq subset_antisym var_subst_dom_def)
  show ?case
    by (simp add: \<open>\<sigma>=id\<close>)
next
  case (Cons x V)
  consider (main) "x \<noteq> \<sigma> x" "x \<notin> set V" | (x_\<sigma>x) "x = \<sigma> x" | (x_V) "x \<in> set V"
    by auto
  then show ?case
  proof cases
    case main
    obtain z where [simp]: "compatible x z" and [simp]: "z \<noteq> x" and [simp]: "z \<noteq> \<sigma> x"
      and [simp]: "z \<notin> vars c" and [simp]: "z \<notin> set V" and "z \<notin> \<sigma> ` vars c" 
      and [simp]: "z \<notin> \<sigma> ` set V" and [simp]: "z \<notin> vars (subst_vars \<sigma> c)"
      and [simp]: "z \<noteq> \<sigma> (\<sigma> x)"
      apply atomize_elim
      apply (rule fresh_compatible)
      by simp

    have [simp]: "inj_on (transpose x z) A" for A
      by simp

    define \<sigma>x where "\<sigma>x = \<sigma>(x:=x)"

    have [simp]: \<open>valid_var_subst \<sigma>\<close>
      using Cons.prems by -
    have valid_\<sigma>x[simp]: "valid_var_subst \<sigma>x"
      by (simp add: Cons.prems(1) \<sigma>x_def) 
    have [simp]: \<open>no_conflict \<sigma> c\<close>
      using Cons.prems by -
    have inj_\<sigma>x[simp]: "inj_on \<sigma>x (set V)"
      by (metis Cons.prems(2) \<sigma>x_def fun_upd_other inj_on_cong inj_on_subset main(2) set_subset_Cons)
    have \<open>\<sigma> x \<notin> \<sigma> ` set V\<close>
      using Cons.prems(2) \<open>x \<notin> set V\<close> by auto
    have [simp]: \<open>compatible (\<sigma> x) z\<close>
      using Cons.prems(1) \<open>compatible x z\<close> compatible_sym compatible_trans valid_var_subst_def by blast
    have [simp]: "vars (foldr Local V c) = vars c \<union> set V" for V c
      by (induction V, auto)
    have [simp]: "\<sigma> z = z"
      using \<open>z \<notin> set V\<close> \<open>z \<noteq> x\<close> Cons.prems unfolding var_subst_dom_def by auto

    obtain c' where "c =a= c'" and avoidc': "localvars c' \<inter> ({x,z,\<sigma> x} \<union> \<sigma> ` set V) = {}"
      apply (atomize_elim, rule alpha_rename_fresh)
      unfolding var_subst_dom_def by simp  

    have [simp]: "no_conflict \<sigma> c'"
      apply (rule localvars_dom_no_conflict)
      using avoidc' Cons.prems(4) by auto
    have [simp]: "var_subst_dom \<sigma>x \<subseteq> set V"
      by (smt Cons.prems(4) \<sigma>x_def fun_upd_apply insert_iff list.simps(15) mem_Collect_eq subset_iff var_subst_dom_def)
    have [simp]: "no_conflict \<sigma>x (full_subst_vars (transpose x z) c')"
      apply (rule localvars_dom_no_conflict)
      apply (subst fv_full_subst_vars)
      using avoidc'[THEN equals0D] \<open>var_subst_dom \<sigma>x \<subseteq> set V\<close>[THEN subsetD]
        apply (auto simp: var_subst_dom_def transpose_def \<sigma>x_def dest!: )
      by (meson imageI)
    have [simp]: "var_subst_dom (transpose x z) \<inter> localvars c' = {}"
      using \<open>z \<noteq> x\<close>[symmetric] avoidc' by auto
    have [simp]: "var_subst_dom (transpose (\<sigma> x) z) \<inter> localvars c' = {}"
      by (smt (verit) Un_insert_left avoidc' disjoint_iff_not_equal insertCI mem_Collect_eq transpose_apply_other var_subst_dom_def)
    have [simp]: "no_conflict (transpose x z) c'"
      apply (rule localvars_dom_no_conflict)
      apply auto
      by (metis \<open>var_subst_dom (Transposition.transpose x z) \<inter> localvars c' = {}\<close> avoidc' disjoint_iff_not_equal inf_sup_ord(3) insert_commute insert_subset transpose_eq_iff)
    have [simp]: "no_conflict (transpose (\<sigma> x) z) c'"
      apply (rule localvars_dom_no_conflict)
      apply auto
      by (metis Un_upper1 \<open>var_subst_dom (Transposition.transpose (\<sigma> x) z) \<inter> localvars c' = {}\<close> avoidc' disjoint_iff insert_subset transpose_eq_iff)

    have disj': "(fv (full_subst_vars (transpose x z) c') - set V) \<inter> set (map \<sigma>x V) = {}"
    proof (rule equals0I)
      fix v assume "v \<in> (fv (full_subst_vars (transpose x z) c') - set V) \<inter> set (map \<sigma>x V)"

      then have vc: "v \<in> transpose x z ` fv c" 
        and vV: "v \<notin> set V" and v\<sigma>: "v \<in> \<sigma>x ` set V"
        using \<open>c =a= c'\<close> by (auto simp: fv_full_subst_vars fv_alpha)

      have "z \<notin> fv c"
        using \<open>z \<notin> vars c\<close> fv_vars by blast
      then have "transpose x z z \<notin> transpose x z ` fv c"
        using \<open>\<And>A. inj_on (transpose x z) A\<close> by blast
      then have "x \<notin> transpose x z ` fv c"
        by simp
      with vc have "v \<noteq> x"
        by metis
  
      from v\<sigma> have "v \<noteq> z"
        unfolding \<sigma>x_def apply auto
        using \<open>z \<notin> \<sigma> ` set V\<close> by blast

      from vc have "transpose x z v \<in> fv c"
        by (simp add: in_transpose_image_iff)
      with \<open>v \<noteq> z\<close> \<open>v \<noteq> x\<close>
      have "v \<in> fv c"
        by simp

      from Cons.prems
      have "(fv c - set (x # V)) \<inter> set (map \<sigma> (x # V)) = {}"
        by -
      moreover have "v \<in> (fv c - set (x # V)) \<inter> set (map \<sigma> (x # V))"
        using \<open>v \<in> fv c\<close> \<open>v \<noteq> x\<close> \<open>v \<notin> set V\<close> apply auto
        using \<sigma>x_def v\<sigma> by auto

      ultimately
      show False
        by simp
    qed
    have [simp]: "z \<notin> fv c'"
      apply (subst fv_alpha[where d=c])
       apply (simp add: \<open>c =a= c'\<close> alpha_eq_sym)
      using \<open>z \<notin> vars c\<close> fv_vars by blast

    have *: "(\<sigma>x \<circ> transpose x z) v =
           (transpose (\<sigma> x) z \<circ> \<sigma> \<circ> inv (transpose (\<sigma> x) z) \<circ> transpose (\<sigma> x) z) v"
      if "v \<in> fv c'" for v
    proof -
      have [simp]: "v \<noteq> z"
        using that \<open>z \<notin> fv c'\<close> by blast
      have [simp]: "\<sigma> v \<noteq> z"
        using \<open>c =a= c'\<close> \<open>z \<notin> \<sigma> ` vars c\<close> fv_alpha fv_vars that by blast
      have [simp]: "\<sigma> x \<noteq> z"
        using \<open>z \<noteq> \<sigma> x\<close> by blast
      consider (vx) "v = x" | (v\<sigma>x) "v = \<sigma> x" "v \<noteq> x" "\<sigma> (\<sigma> x) \<noteq> \<sigma> x"
        | (\<sigma>\<sigma>x) "\<sigma> (\<sigma> x) = \<sigma> x" "\<sigma> x \<noteq> x" "v = \<sigma> x" "v \<noteq> x"
        | (tmp) "v \<noteq> x" "v \<noteq> \<sigma> x"
        by auto
      then show ?thesis
      proof cases
        case vx
        then show ?thesis
          using \<open>x \<noteq> \<sigma> x\<close> \<open>z \<noteq> x\<close>[symmetric] \<sigma>x_def by simp
      next 
        case v\<sigma>x
        then show ?thesis
          using \<open>z \<noteq> \<sigma> (\<sigma> x)\<close>[symmetric] \<open>z \<noteq> \<sigma> x\<close>[symmetric] \<sigma>x_def by simp
      next
        case tmp
        then have [simp]: "\<sigma> v \<noteq> \<sigma> x"
          by (smt Cons.prems(2) Cons.prems(4) Int_Collect in_mono inf_top.left_neutral inj_onD iso_tuple_UNIV_I list.set_intros(1) var_subst_dom_def)
        from tmp show ?thesis
          using \<sigma>x_def by simp
      next
        case \<sigma>\<sigma>x

        from that
        have vc: "v \<in> fv c"
          using \<open>c =a= c'\<close> fv_alpha by blast
        from \<sigma>\<sigma>x show ?thesis
          unfolding \<sigma>x_def apply auto
          using Cons.prems vc apply auto
          by (metis \<open>\<sigma> x \<notin> \<sigma> ` set V\<close> imageI)
      qed
    qed

    have swap_subst: 
      "subst_vars \<sigma>x (full_subst_vars (transpose x z) c')
     = full_subst_vars (transpose (\<sigma> x) z) (subst_vars \<sigma> c')"
      apply (subst full_subst_vars_subst_vars_comm) apply simp_all[3]
      apply (subst full_subst_vars_subst_vars_eq) apply simp
      apply (subst full_subst_vars_subst_vars_eq) apply simp
      apply (subst subst_vars_compose) apply simp_all[3]
      apply (subst subst_vars_compose) apply (simp_all add: valid_var_subst_comp)[3]
      apply (rule subst_vars_cong) apply (simp add: valid_var_subst_comp)
      using * by -

    have "full_subst_vars (transpose x z) (foldr Local V c)
     = foldr Local V (full_subst_vars (transpose x z) c)"
      using \<open>x \<notin> set V\<close> \<open>z \<notin> set V\<close>
      by (induction V, auto)
    also have "\<dots> =a= foldr Local V (full_subst_vars (transpose x z) c')"
      apply (rule alpha_foldr_Local_cong)
      apply (rule alpha_eq_full_subst)
      using \<open>c =a= c'\<close> by auto
    also have "\<dots> =a= foldr Local (map \<sigma>x V) (subst_vars \<sigma>x (full_subst_vars (transpose x z) c'))"
      apply (rule Cons.IH)
      using disj' by auto
    also have "\<dots> =a= foldr Local (map \<sigma>x V) (full_subst_vars (transpose (\<sigma> x) z) (subst_vars \<sigma> c'))"
      apply (rule alpha_foldr_Local_cong)
      using swap_subst by simp
    also have "\<dots> =a= full_subst_vars (transpose (\<sigma> x) z) (foldr Local (map \<sigma>x V) (subst_vars \<sigma> c'))"
      using \<open>\<sigma> x \<notin> \<sigma> ` set V\<close> \<open>z \<notin> \<sigma> ` set V\<close>
      apply (induction V)
      by (auto simp: \<sigma>x_def)
    also have "\<dots> = full_subst_vars (transpose (\<sigma> x) z) (foldr Local (map \<sigma> V) (subst_vars \<sigma> c'))"
      by (simp add: \<open>x \<notin> set V\<close> \<sigma>x_def)
    also have "\<dots> =a= full_subst_vars (transpose (\<sigma> x) z) (foldr Local (map \<sigma> V) (subst_vars \<sigma> c))"
      apply (rule alpha_eq_full_subst, auto)
      apply (rule alpha_foldr_Local_cong)
      using \<open>c =a= c'\<close>[symmetric] by (rule subst_vars_alpha_eq, auto)

    finally show ?thesis
      unfolding Cons
       apply simp
       apply (rule ae_Local[where z=z])
      by (simp_all add: id_def)
  next
    case x_\<sigma>x
    show ?thesis
      apply (simp add: x_\<sigma>x[symmetric])
      apply (rule alpha_Local_cong)
      apply (rule Cons.IH)
      using Cons.prems x_\<sigma>x apply auto
      by (metis (mono_tags) x_\<sigma>x insert_iff mem_Collect_eq subsetD var_subst_dom_def)
  next
    case x_V

    obtain z where [simp]: "compatible x z" and [simp]: "z \<notin> fv c"
      and [simp]: "z \<notin> fv (subst_vars \<sigma> c)"
      apply atomize_elim
      apply (rule fresh_compatible)
      by simp
    then have [simp]: "compatible z (\<sigma> x)"
      using Cons.prems(1) compatible_sym compatible_trans valid_var_subst_def by blast

    have *: "foldr Local V c =a= foldr Local (map \<sigma> V) (subst_vars \<sigma> c)"
      apply (rule Cons.IH)
      using Cons.prems using x_V by auto

    have "foldr Local (x # V) c = Local x (foldr Local V c)"
      by simp
    also have "\<dots> =a= Local z (foldr Local V c)"
      apply (rule alpha_eq_local_unused)
      using x_V by simp_all
    also have "\<dots> =a= Local z (foldr Local (map \<sigma> V) (subst_vars \<sigma> c))"
      using * by (rule alpha_Local_cong)
    also have "\<dots> =a= Local (\<sigma> x) (foldr Local (map \<sigma> V) (subst_vars \<sigma> c))"
      apply (rule alpha_eq_local_unused)
      using x_V by simp_all
    also have "\<dots> =a= foldr Local (map \<sigma> (x # V)) (subst_vars \<sigma> c)"
      by simp
    finally show ?thesis
      by -
  qed
qed

end
