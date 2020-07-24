theory Rename_Locals
  imports Alpha_Equivalence
begin


lemma full_subst_vars_subst_vars:
  assumes "valid_var_subst \<sigma>"
  assumes "inj_on \<sigma> (vars p)"
  assumes "var_subst_dom \<sigma> \<inter> vars p \<inter> \<sigma> -` vars p = {}"
  shows "full_subst_vars \<sigma> p =d= subst_vars \<sigma> p"
  apply (insert assms)
proof (induction p arbitrary: \<sigma>)
  case (IfTE e p1 p2)
  have inj: "inj_on \<sigma> (vars p1)" "inj_on \<sigma> (vars p2)"
    using IfTE.prems(2)
    by (simp_all add: inj_on_Un) 
  have IH1: "full_subst_vars \<sigma> p1 =d= subst_vars \<sigma> p1"
    apply (rule IfTE.IH)
    using IfTE.prems(1,3) inj by auto
  have IH2: "full_subst_vars \<sigma> p2 =d= subst_vars \<sigma> p2"
    apply (rule IfTE.IH)
    using IfTE.prems(1,3) inj by auto
  show ?case
    apply simp using IH1 IH2
    using denot_eq_ifte_cong1 denot_eq_ifte_cong2 locals.R_trans by blast 
next
  case (Seq p1 p2)
  have inj: "inj_on \<sigma> (vars p1)" "inj_on \<sigma> (vars p2)"
    using Seq.prems(2)
    by (simp_all add: inj_on_Un) 
  have IH1: "full_subst_vars \<sigma> p1 =d= subst_vars \<sigma> p1"
    apply (rule Seq.IH)
    using Seq.prems inj by auto
  have IH2: "full_subst_vars \<sigma> p2 =d= subst_vars \<sigma> p2"
    apply (rule Seq.IH)
    using Seq.prems inj by auto
  show ?case
    apply simp using IH1 IH2
    using denot_eq_seq_cong1 denot_eq_seq_cong2 locals.R_trans by blast
next
  case (While e p)
  have inj: "inj_on \<sigma> (vars p)"
    using While.prems(2)
    by (simp_all add: inj_on_Un) 
  have IH: "full_subst_vars \<sigma> p =d= subst_vars \<sigma> p"
    apply (rule While.IH)
    using While.prems inj by auto
  then show ?case
    apply simp using IH
    using denot_eq_while_cong by auto
next
  case (Local v p)
  show ?case
  proof (cases "v \<in> var_subst_dom \<sigma>")
    case True
    define w \<sigma>'
      where "w = \<sigma> v"
        and "\<sigma>' = \<sigma>(v:=v)"

    from Local.prems(3)
    have \<sigma>_id: "v \<in> \<sigma> ` vars p \<Longrightarrow> v = \<sigma> v"
      unfolding var_subst_dom_def apply auto
      by (smt Int_insert_right_if1 insertI1 insert_disjoint(2) mem_Collect_eq mk_disjoint_insert vimageI)
    then have inj: "inj_on \<sigma>' (vars p)"
      apply (rule_tac inj_onI)
        unfolding \<sigma>'_def 
        apply auto
        by (metis Local.prems(2) image_eqI inj_onD insert_iff vars.simps(4)) 

    have "v \<noteq> w"
      by (metis (mono_tags) True mem_Collect_eq var_subst_dom_def w_def)
    have compat_vw: "compatible v w"
      using Local.prems(1) valid_var_subst_def w_def by blast

    have \<open>w \<notin> fv p\<close>
      using Local.prems(3) True fv_vars subsetD w_def by fastforce
    have valid_\<sigma>[simp]: "valid_var_subst \<sigma>"
      by (simp add: Local.prems(1))
    have valid_\<sigma>'[simp]: "valid_var_subst \<sigma>'"
      by (simp add: \<sigma>'_def)
    have valid_\<sigma>'vw: "valid_var_subst (id(v := w, w := v) \<circ> \<sigma>')"
      using valid_\<sigma> unfolding o_def \<sigma>'_def valid_var_subst_def w_def apply auto
      using compatible_trans apply blast
      by (metis compatible_sym compatible_trans w_def)
    have valid_\<sigma>v: "valid_var_subst (\<sigma>(v:=v))"
      using \<open>valid_var_subst \<sigma>'\<close> \<sigma>'_def by blast

    have "w \<notin> vars (full_subst_vars \<sigma>' p)"
      apply (subst vars_full_subst_vars, simp)
      unfolding \<sigma>'_def apply auto
      (* Sledgehammer proof *)
      using \<open>v \<noteq> w\<close> apply blast
      using Local.prems(2) w_def by auto
    then have w_fv_\<sigma>'p: "w \<notin> fv (full_subst_vars \<sigma>' p)"
      using fv_vars by blast

    have \<sigma>'_disj: "var_subst_dom \<sigma>' \<inter> vars p \<inter> \<sigma>' -` vars p = {}"
      apply (rule equals0I)
      using Local.prems(3)[THEN equals0D]
      apply (simp add: var_subst_dom_def \<sigma>'_def fun_upd_def) by metis

    have "full_subst_vars \<sigma> (Local v p)
          = full_subst_vars (id(v:=w,w:=v)) (full_subst_vars \<sigma>' (Local v p))"
      apply (subst full_subst_vars_compose, simp)
      apply (subst full_subst_vars_cong[where \<sigma>="id(v := w, w := v) \<circ> \<sigma>'" and \<tau>=\<sigma>])
        apply (fact valid_\<sigma>'vw)
       apply (auto simp: \<sigma>'_def w_def Fun.swap_def o_def id_def)
      (* Sledgehammer proof *)
      using \<sigma>_id apply blast
      by (metis Local.prems(2) inj_onD insert_iff vars.simps(4))
    also have "\<dots> = full_subst_vars (id(v:=w,w:=v)) (Local v (full_subst_vars \<sigma>' p))"
      by (simp add: \<sigma>'_def)
    also have "\<dots> =d= Local v (full_subst_vars \<sigma>' p)"
      apply (rule full_subst_vars_id)
        apply (metis bij_betw_id bij_swap_iff id_apply swap_def)
       apply (simp add: compat_vw compatible_sym valid_var_subst_def)
      by (auto simp: w_fv_\<sigma>'p var_subst_dom_def)
    also have "\<dots> =d= Local v (subst_vars \<sigma>' p)"
      apply (rule denot_eq'_cong_local)
      apply (rule Local.IH)
      by (simp_all add: inj \<sigma>'_disj)
    also have "\<dots> = subst_vars \<sigma> (Local v p)"
      apply simp
      apply (subst subst_vars_cong[where \<sigma>="\<sigma>(v:=v)" and \<tau>=\<sigma>'])
        apply (fact valid_\<sigma>v)
      using \<open>w \<notin> fv p\<close> unfolding \<sigma>'_def w_def Fun.swap_def by auto
    finally show ?thesis
      by -
  next
    case False
    then have [simp]: "\<sigma> v = v"
      by (simp add: var_subst_dom_def)
    define swap_p subst_p
      where "swap_p = full_subst_vars \<sigma> p"
        and "subst_p = subst_vars \<sigma> p"

    have "full_subst_vars \<sigma> (Local v p) = Local v swap_p"
      by (simp add: swap_p_def)
    also have "\<dots> =d= Local v subst_p"
      apply (rule denot_eq'_cong_local)
      unfolding swap_p_def subst_p_def
      apply (rule Local.IH)
      using Local.prems by auto
    also have "\<dots> = subst_vars \<sigma> (Local v p)"
      unfolding subst_p_def
      apply simp
      by (metis \<open>\<sigma> v = v\<close> fun_upd_triv)
    finally show ?thesis
      by -
  qed
qed auto

lemma alpha_denot_eq:
  assumes "p1 =a= p2"
  shows "p1 =d= p2"
  using assms
proof (induction)
  case (ae_IfTE p1 p1' p2 p2' e)
  then show ?case
    using denot_eq_ifte_cong1 denot_eq_ifte_cong2 locals.R_trans by blast
next
  case (ae_While p p' e)
  then show ?case
    using denot_eq_while_cong by blast
next
  case (ae_Seq p1 p1' p2 p2')
  then show ?case
    using denot_eq_seq_cong1 denot_eq_seq_cong2 locals.R_trans by blast
next
  case (ae_Local y z x p1 p2)

  have valid_xz: "valid_var_subst (Fun.swap x z id)"
    using ae_Local.hyps
    unfolding valid_var_subst_def apply auto
    by (metis ae_Local.hyps(2) compatible_refl compatible_sym id_apply swap_apply(1) swap_apply(2) swap_apply(3))
  have valid_yz: "valid_var_subst (Fun.swap y z id)"
    using ae_Local.hyps
    unfolding valid_var_subst_def apply auto
    by (metis compatible_refl compatible_sym id_apply swap_apply(1) swap_apply(2) swap_apply(3))

  have inj_xz: "inj_on (Fun.swap x z id) (vars (Local x p1))"
    apply (rule inj_onI)
    by (simp add: inj_eq)
  have inj_yz: "inj_on (Fun.swap y z id) (vars (Local y p2))"
    apply (rule inj_onI)
    by (simp add: inj_eq)

  have disj_xz: "var_subst_dom (Fun.swap x z id) \<inter> vars (Local x p1)
                 \<inter> Fun.swap x z id -` vars (Local x p1) = {}"
    apply (subst bij_vimage_eq_inv_image)
    using ae_Local.hyps apply auto
    apply (metis id_apply swap_apply(2) swap_apply(3) swap_commute)
    by (smt id_apply mem_Collect_eq swap_apply(3) var_subst_dom_def)
  have disj_yz: "var_subst_dom (Fun.swap y z id) \<inter> vars (Local y p2)
                 \<inter> Fun.swap y z id -` vars (Local y p2) = {}"
    apply (subst bij_vimage_eq_inv_image)
    using ae_Local.hyps apply auto
    apply (metis id_apply swap_apply(2) swap_apply(3) swap_commute)
    by (smt id_apply mem_Collect_eq swap_apply(3) var_subst_dom_def)

  have "Local x p1 = Local x (subst_vars id p1)"
    by (metis (full_types) eq_id_iff subst_vars_id)
  also have "\<dots> = subst_vars (Fun.swap x z id) (Local x p1)"
    apply simp
    apply (rule subst_vars_cong)
     apply (simp add: valid_var_subst_def)
    by (metis ae_Local.hyps(5) fun_upd_apply fv_vars id_apply subsetD swap_apply(3))
  also have "\<dots> =d= full_subst_vars (Fun.swap x z id) (Local x p1)"
    apply (rule denot_eq'_sym)
    using valid_xz inj_xz disj_xz by (rule full_subst_vars_subst_vars)
  also have "\<dots> =d= Local z (full_subst_vars (Fun.swap x z id) p1)"
    by simp
  also from ae_Local.IH
  have "\<dots> =d= Local z (full_subst_vars (Fun.swap y z id) p2)"
    by (rule denot_eq'_cong_local)
  also have "\<dots> =d= full_subst_vars (Fun.swap y z id) (Local y p2)"
    by simp
  also have "\<dots> =d= subst_vars (Fun.swap y z id) (Local y p2)"
    using valid_yz inj_yz disj_yz by (rule full_subst_vars_subst_vars)
  also have "\<dots> = Local y (subst_vars id p2)"
    apply (rule sym, simp)
    apply (rule subst_vars_cong)
     apply (simp add: valid_var_subst_def)
    by (metis ae_Local.hyps(6) fun_upd_apply fv_vars id_apply subsetD swap_apply(3))
  also have "\<dots> = Local y p2"
    using eq_id_iff by fastforce
  finally
  show ?case by -
qed auto

lemma qrhl_subst_left:
  assumes [simp]: "bij \<tau>" and [simp]: "valid_var_subst \<tau>"
  shows "qRHL A c d B \<longleftrightarrow>
        qRHL (substp_bij (idx_var_subst True \<tau>) A) (full_subst_vars \<tau> c) d
             (substp_bij (idx_var_subst True \<tau>) B)"
proof
  assume "qRHL A c d B"
  then show "qRHL (substp_bij (idx_var_subst True \<tau>) A) (full_subst_vars \<tau> c) d
             (substp_bij (idx_var_subst True \<tau>) B)"
    unfolding qRHL_def apply simp
    apply (rule qrhl_subst_left0)
    by (auto simp add: program.intros(3) program_substitute)
next
  define \<tau>1 where "\<tau>1 = idx_var_subst True \<tau>"
  have [simp]: "bij (inv \<tau>)"
    by (simp add: bij_betw_inv_into)
  have [simp]: "bij \<tau>1"
    by (simp add: \<tau>1_def)
  have [simp]: "bij (inv \<tau>1)"
    by (simp add: bij_betw_inv_into)
  have [simp]: "valid_var_subst (inv \<tau>)"
    by (metis assms(1) assms(2) bij_pointE bijection.intro bijection.inv_left compatible_sym valid_var_subst_def)
  have [simp]: "valid_var_subst \<tau>1"
    by (simp add: \<tau>1_def)
  have [simp]: "valid_var_subst (inv \<tau>1)"
    by (metis (full_types) \<open>bij \<tau>1\<close> \<open>valid_var_subst \<tau>1\<close> bij_betw_imp_surj compatible_sym surj_f_inv_f valid_var_subst_def)
  have [simp]: "inv \<tau> \<circ> \<tau> = id"
    using assms(1) bijection.intro bijection.inv_comp_left by blast
  have [simp]: "inv \<tau>1 \<circ> \<tau>1 = id"
    using \<open>bij \<tau>1\<close> bijection.intro bijection.inv_comp_left by blast
  have [simp]: "substp_bij (inv \<tau>1) (substp_bij \<tau>1 A) = A" for A
    by (subst substp_bij_comp, auto)
  have inv_\<tau>1: "inv \<tau>1 = idx_var_subst True (inv \<tau>)"
    unfolding \<tau>1_def apply (rule inv_idx_var_subst) by simp
  
  assume "qRHL (substp_bij \<tau>1 A) (full_subst_vars \<tau> c) d
             (substp_bij \<tau>1 B)"
  then have "qRHL (substp_bij (inv \<tau>1) (substp_bij \<tau>1 A))
                  (full_subst_vars (inv \<tau>) (full_subst_vars \<tau> c))
                  d
                  (substp_bij (inv \<tau>1) (substp_bij \<tau>1 B))"
    unfolding qRHL_def substitute_full_subst_vars_Skip inv_\<tau>1
    apply (rule_tac qrhl_subst_left0)
    by (auto intro: program.intros)
  then show "qRHL A c d B"
    by auto
qed

lemma qrhl_subst_right:
  assumes [simp]: "bij \<tau>" and [simp]: "valid_var_subst \<tau>"
  shows "qRHL A c d B \<longleftrightarrow>
        qRHL (substp_bij (idx_var_subst False \<tau>) A) c (full_subst_vars \<tau> d)
             (substp_bij (idx_var_subst False \<tau>) B)"
proof
  assume "qRHL A c d B"
  then show "qRHL (substp_bij (idx_var_subst False \<tau>) A) c (full_subst_vars \<tau> d)
             (substp_bij (idx_var_subst False \<tau>) B)"
    unfolding qRHL_def apply simp
    apply (rule qrhl_subst_right0)
    by (auto simp add: program.intros(3) program_substitute)
next
  define \<tau>2 where "\<tau>2 = idx_var_subst False \<tau>"
  have [simp]: "bij (inv \<tau>)"
    by (simp add: bij_betw_inv_into)
  have [simp]: "bij \<tau>2"
    by (simp add: \<tau>2_def)
  have [simp]: "bij (inv \<tau>2)"
    by (simp add: bij_betw_inv_into)
  have [simp]: "valid_var_subst (inv \<tau>)"
    by (metis assms(1) assms(2) bij_pointE bijection.intro bijection.inv_left compatible_sym valid_var_subst_def)
  have [simp]: "valid_var_subst \<tau>2"
    by (simp add: \<tau>2_def)
  have [simp]: "valid_var_subst (inv \<tau>2)"
    by (metis (full_types) \<open>bij \<tau>2\<close> \<open>valid_var_subst \<tau>2\<close> bij_betw_imp_surj compatible_sym surj_f_inv_f valid_var_subst_def)
  have [simp]: "inv \<tau> \<circ> \<tau> = id"
    using assms(1) bijection.intro bijection.inv_comp_left by blast
  have [simp]: "inv \<tau>2 \<circ> \<tau>2 = id"
    using \<open>bij \<tau>2\<close> bijection.intro bijection.inv_comp_left by blast
  have [simp]: "substp_bij (inv \<tau>2) (substp_bij \<tau>2 A) = A" for A
    by (subst substp_bij_comp, auto)
  have inv_\<tau>2: "inv \<tau>2 = idx_var_subst False (inv \<tau>)"
    unfolding \<tau>2_def apply (rule inv_idx_var_subst) by simp
  
  assume "qRHL (substp_bij \<tau>2 A) c (full_subst_vars \<tau> d)
             (substp_bij \<tau>2 B)"
  then have "qRHL (substp_bij (inv \<tau>2) (substp_bij \<tau>2 A))
                  c
                  (full_subst_vars (inv \<tau>) (full_subst_vars \<tau> d))
                  (substp_bij (inv \<tau>2) (substp_bij \<tau>2 B))"
    unfolding qRHL_def substitute_full_subst_vars_Skip inv_\<tau>2
    apply (rule_tac qrhl_subst_right0)
    by (auto intro: program.intros)
  then show "qRHL A c d B"
    by auto
qed

lemma rename_qrhl_left:
  assumes valid[simp]: "valid_var_subst \<sigma>"
  assumes [simp]: "no_conflict \<sigma> c"
  assumes inj: "inj_on \<sigma> (fv c \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
  defines "\<sigma>1 \<equiv> idx_var_subst True \<sigma>"
  shows "qRHL A c d B \<longleftrightarrow>
         qRHL (substp \<sigma>1 A) (subst_vars \<sigma> c) d (substp \<sigma>1 B)"
proof -
  (* In order to get a substitution with finite support *)
  define \<sigma>' \<sigma>'1 where "\<sigma>' x = (if x \<in> deidx1 (fvp A) \<union> deidx1 (fvp B) \<union> fv c then \<sigma> x else x)" 
    and "\<sigma>'1 = idx_var_subst True \<sigma>'" for x
  have valid\<sigma>'[simp]: "valid_var_subst \<sigma>'"
    using valid unfolding valid_var_subst_def \<sigma>'_def by auto
  have valid\<sigma>1[simp]: "valid_var_subst \<sigma>1"
    unfolding \<sigma>1_def by simp
  have valid\<sigma>'1[simp]: "valid_var_subst \<sigma>'1"
    unfolding \<sigma>'1_def by simp
  have [simp]: "x \<in> fvp A \<union> fvp B \<Longrightarrow> \<sigma>'1 x = \<sigma>1 x" for x
    unfolding \<sigma>1_def \<sigma>'1_def \<sigma>'_def deidx_def unfolding idx_var_subst_def by auto
  have [simp]: "inj_on \<sigma>'1 (fvp A)"
    unfolding \<sigma>'1_def apply (rule inj_on_idx_var_subst1, simp)
    using inj by (simp add: \<sigma>'_def inj_on_def)    
  have [simp]: "inj_on \<sigma>'1 (fvp B)"
    unfolding \<sigma>'1_def apply (rule inj_on_idx_var_subst1, simp)
    using inj by (simp add: \<sigma>'_def inj_on_def) 

  obtain c' where "c =a= c'" 
    and c'avoid: "localvars c' \<inter> 
                  (var_subst_dom \<sigma>' \<union> 
                   \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>) \<union>
                   \<sigma>' ` (deidx1 (fvp A) \<union> deidx1 (fvp B) \<union> fv c) \<union>
                   deidx1 (fvp A) \<union> deidx1 (fvp B) \<union> fv c) = {}"
    apply (atomize_elim, rule alpha_rename_fresh)
    unfolding var_subst_dom_def \<sigma>'_def by simp

  have fv_cc': "fv c' = fv c"
    using \<open>c =a= c'\<close>
    by (simp add: fv_alpha)

  have [simp]: "no_conflict \<sigma> c'"
    apply (rule localvars_dom_no_conflict)
    unfolding fv_cc'
    using c'avoid by auto

  have inj': "inj_on \<sigma>' (vars c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
  proof -
    have inj_id: "inj_on f X" if "\<forall>x\<in>X. f x = x" for f and X :: "'z set"
      by (metis inj_onI that)
    from c'avoid 
    have "inj_on \<sigma>' (localvars c')"
      apply (rule_tac inj_id)
      unfolding var_subst_dom_def by auto
    moreover 
    have "inj_on \<sigma>' (fv c \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
      apply (rule inj_on_cong[THEN iffD1, of _ \<sigma>])
      unfolding \<sigma>'_def using inj by auto
    then have "inj_on \<sigma>' (fv c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
      using \<open>c =a= c'\<close> by (simp add: fv_alpha)
    moreover
    have "\<sigma>' ` (localvars c' - (fv c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))) \<inter>
            \<sigma>' ` (fv c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B) - (localvars c')) =
            {}" (is "?left \<inter> ?right = {}")
    proof -
      from c'avoid have "var_subst_dom \<sigma>' \<inter> localvars c' = {}"
        by auto
      then have "\<sigma>' ` localvars c' \<subseteq> localvars c'"
        unfolding var_subst_dom_def using mk_disjoint_insert by fastforce
      then have "?left \<subseteq> localvars c'"
        by auto
      moreover have "?right \<subseteq> \<sigma>' ` (fv c \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
        unfolding fv_cc' by blast
      moreover have "(localvars c') \<inter> \<sigma>' ` (fv c \<union> deidx1 (fvp A) \<union> deidx1 (fvp B)) = {}"
        using c'avoid by auto
      ultimately show ?thesis
        by auto
    qed
    ultimately have "inj_on \<sigma>' ((localvars c') \<union> (fv c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B)))"
      by (rule_tac inj_on_Un[THEN iffD2], simp)
    then show ?thesis
      unfolding vars_fv_localvars
      by (simp add: sup.assoc sup.left_commute)
  qed

  have "finite (vars c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B))"
    by simp
  then obtain \<tau> where \<tau>\<sigma>': "\<And>x. x \<in> vars c' \<union> deidx1 (fvp A) \<union> deidx1 (fvp B) \<Longrightarrow> \<tau> x = \<sigma>' x" 
      and "bij \<tau>" and "valid_var_subst \<tau>"
    using extend_var_subst[OF inj' valid\<sigma>'] by metis
  define \<tau>1 where "\<tau>1 = idx_var_subst True \<tau>"
  have \<tau>\<sigma>'1: "\<And>x. x \<in> fvp A \<union> fvp B \<Longrightarrow> \<tau>1 x = \<sigma>'1 x"
    unfolding \<tau>1_def \<sigma>'1_def using \<tau>\<sigma>'
    unfolding idx_var_subst_def deidx_def by auto
  have "bij \<tau>1" and "valid_var_subst \<tau>1"
    unfolding \<tau>1_def using \<open>bij \<tau>\<close> and \<open>valid_var_subst \<tau>\<close> by auto

  define eq where "eq = (\<longleftrightarrow>)"
  write eq (infix "\<leftrightarrow>" 50)
  have [trans]: "p \<leftrightarrow> qRHL A c d B \<Longrightarrow> c =d= c' \<Longrightarrow> p \<leftrightarrow> qRHL A c' d B" for p A c c' d B
    by (simp add: denot_eq_qrhl_left)
  have [trans]: "p \<leftrightarrow> qRHL A c d B \<Longrightarrow> c =a= c' \<Longrightarrow> p \<leftrightarrow> qRHL A c' d B" for p A c c' d B
    using alpha_denot_eq denot_eq_qrhl_left by fastforce

  have "qRHL A c d B \<leftrightarrow> 
        qRHL (substp_bij \<tau>1 A) (full_subst_vars \<tau> c) d
             (substp_bij \<tau>1 B)"
    unfolding \<tau>1_def
    apply (subst qrhl_subst_left[symmetric])
    using \<open>bij \<tau>\<close> \<open>valid_var_subst \<tau>\<close> eq_def by auto
  also have "substp_bij \<tau>1 A = substp \<sigma>'1 A"
    using \<open>bij \<tau>1\<close> \<open>valid_var_subst \<tau>1\<close> \<tau>\<sigma>'1 substp_substp_bij by auto
  also have "substp_bij \<tau>1 B = substp \<sigma>'1 B"
    using \<open>bij \<tau>1\<close> \<open>valid_var_subst \<tau>1\<close> \<tau>\<sigma>'1 substp_substp_bij by auto
  also have "substp \<sigma>'1 A = substp \<sigma>1 A"
    by (rule substp_cong, auto)
  also have "substp \<sigma>'1 B = substp \<sigma>1 B"
    by (rule substp_cong, auto)
  also have "full_subst_vars \<tau> c =a= full_subst_vars \<tau> c'"
    using \<open>valid_var_subst \<tau>\<close> _ \<open>c =a= c'\<close> apply (rule alpha_eq_full_subst)
    using \<open>bij \<tau>\<close> bij_betw_imp_inj_on by blast
  also have "full_subst_vars \<tau> c' =d= full_subst_vars \<sigma>' c'"
    using \<open>valid_var_subst \<tau>\<close> \<tau>\<sigma>' full_subst_vars_cong by fastforce
  also have "full_subst_vars \<sigma>' c' = subst_vars \<sigma>' c'"
    (* Because all locals of c' are fresh *)
    apply (rule full_subst_vars_subst_vars_eq)
    using c'avoid by blast
  also have "subst_vars \<sigma>' c' = subst_vars \<sigma> c'"
    apply (rule subst_vars_cong, simp)
    using \<open>c =a= c'\<close> \<sigma>'_def fv_alpha by auto
  also have "subst_vars \<sigma> c' =a= subst_vars \<sigma> c"
    apply (rule subst_vars_alpha_eq)
    by (auto simp add: \<open>c =a= c'\<close> alpha_eq_sym)
  finally show ?thesis 
    by (simp add: eq_def)
qed

lemma rename_qrhl_right:
  assumes valid[simp]: "valid_var_subst \<sigma>"
  assumes [simp]: "no_conflict \<sigma> d"
  assumes inj: "inj_on \<sigma> (fv d \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
  defines "\<sigma>2 \<equiv> idx_var_subst False \<sigma>"
  shows "qRHL A c d B \<longleftrightarrow>
         qRHL (substp \<sigma>2 A) c (subst_vars \<sigma> d) (substp \<sigma>2 B)"
proof -
  (* In order to get a substitution with finite support *)
  define \<sigma>' \<sigma>'2 where "\<sigma>' x = (if x \<in> deidx2 (fvp A) \<union> deidx2 (fvp B) \<union> fv d then \<sigma> x else x)" 
    and "\<sigma>'2 = idx_var_subst False \<sigma>'" for x
  have valid\<sigma>'[simp]: "valid_var_subst \<sigma>'"
    using valid unfolding valid_var_subst_def \<sigma>'_def by auto
  have valid\<sigma>2[simp]: "valid_var_subst \<sigma>2"
    unfolding \<sigma>2_def by simp
  have valid\<sigma>'2[simp]: "valid_var_subst \<sigma>'2"
    unfolding \<sigma>'2_def by simp
  have [simp]: "x \<in> fvp A \<union> fvp B \<Longrightarrow> \<sigma>'2 x = \<sigma>2 x" for x
    unfolding \<sigma>2_def \<sigma>'2_def \<sigma>'_def deidx_def unfolding idx_var_subst_def by auto
  have [simp]: "inj_on \<sigma>'2 (fvp A)"
    unfolding \<sigma>'2_def apply (rule inj_on_idx_var_subst1, simp)
    using inj by (simp add: \<sigma>'_def inj_on_def)    
  have [simp]: "inj_on \<sigma>'2 (fvp B)"
    unfolding \<sigma>'2_def apply (rule inj_on_idx_var_subst1, simp)
    using inj by (simp add: \<sigma>'_def inj_on_def) 

  obtain d' where "d =a= d'" 
    and d'avoid: "localvars d' \<inter> 
                  (var_subst_dom \<sigma>' \<union> 
                   \<sigma> ` (fv d \<inter> var_subst_dom \<sigma>) \<union>
                   \<sigma>' ` (deidx2 (fvp A) \<union> deidx2 (fvp B) \<union> fv d) \<union>
                   deidx2 (fvp A) \<union> deidx2 (fvp B) \<union> fv d) = {}"
    apply (atomize_elim, rule alpha_rename_fresh)
    unfolding var_subst_dom_def \<sigma>'_def by simp

  have fv_dd': "fv d' = fv d"
    using \<open>d =a= d'\<close>
    by (simp add: fv_alpha)

  have [simp]: "no_conflict \<sigma> d'"
    apply (rule localvars_dom_no_conflict)
    unfolding fv_dd'
    using d'avoid by auto

  have inj': "inj_on \<sigma>' (vars d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
  proof -
    have inj_id: "inj_on f X" if "\<forall>x\<in>X. f x = x" for f and X :: "'z set"
      by (metis inj_onI that)
    from d'avoid 
    have "inj_on \<sigma>' (localvars d')"
      apply (rule_tac inj_id)
      unfolding var_subst_dom_def by auto
    moreover 
    have "inj_on \<sigma>' (fv d \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
      apply (rule inj_on_cong[THEN iffD1, of _ \<sigma>])
      unfolding \<sigma>'_def using inj by auto
    then have "inj_on \<sigma>' (fv d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
      using \<open>d =a= d'\<close> by (simp add: fv_alpha)
    moreover
    have "\<sigma>' ` (localvars d' - (fv d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))) \<inter>
            \<sigma>' ` (fv d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B) - (localvars d')) =
            {}" (is "?left \<inter> ?right = {}")
    proof -
      from d'avoid have "var_subst_dom \<sigma>' \<inter> localvars d' = {}"
        by auto
      then have "\<sigma>' ` localvars d' \<subseteq> localvars d'"
        unfolding var_subst_dom_def using mk_disjoint_insert by fastforce
      then have "?left \<subseteq> localvars d'"
        by auto
      moreover have "?right \<subseteq> \<sigma>' ` (fv d \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
        unfolding fv_dd' by blast
      moreover have "(localvars d') \<inter> \<sigma>' ` (fv d \<union> deidx2 (fvp A) \<union> deidx2 (fvp B)) = {}"
        using d'avoid by auto
      ultimately show ?thesis
        by auto
    qed
    ultimately have "inj_on \<sigma>' ((localvars d') \<union> (fv d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B)))"
      by (rule_tac inj_on_Un[THEN iffD2], simp)
    then show ?thesis
      unfolding vars_fv_localvars
      by (simp add: sup.assoc sup.left_commute)
  qed

  have "finite (vars d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B))"
    by simp
  then obtain \<tau> where \<tau>\<sigma>': "\<And>x. x \<in> vars d' \<union> deidx2 (fvp A) \<union> deidx2 (fvp B) \<Longrightarrow> \<tau> x = \<sigma>' x" 
      and "bij \<tau>" and "valid_var_subst \<tau>"
    using extend_var_subst[OF inj' valid\<sigma>'] by metis
  define \<tau>2 where "\<tau>2 = idx_var_subst False \<tau>"
  have \<tau>\<sigma>'2: "\<And>x. x \<in> fvp A \<union> fvp B \<Longrightarrow> \<tau>2 x = \<sigma>'2 x"
    unfolding \<tau>2_def \<sigma>'2_def using \<tau>\<sigma>'
    unfolding idx_var_subst_def deidx_def by auto
  have "bij \<tau>2" and "valid_var_subst \<tau>2"
    unfolding \<tau>2_def using \<open>bij \<tau>\<close> and \<open>valid_var_subst \<tau>\<close> by auto

  define eq where "eq = (\<longleftrightarrow>)"
  write eq (infix "\<leftrightarrow>" 50)
  have [trans]: "p \<leftrightarrow> qRHL A c d B \<Longrightarrow> d =d= d' \<Longrightarrow> p \<leftrightarrow> qRHL A c d' B" for p A c d' d B
    by (simp add: denot_eq_qrhl_right)
  have [trans]: "p \<leftrightarrow> qRHL A c d B \<Longrightarrow> d =a= d' \<Longrightarrow> p \<leftrightarrow> qRHL A c d' B" for p A c d' d B
    using alpha_denot_eq denot_eq_qrhl_right by fastforce

  have "qRHL A c d B \<leftrightarrow> 
        qRHL (substp_bij \<tau>2 A) c (full_subst_vars \<tau> d)
             (substp_bij \<tau>2 B)"
    unfolding \<tau>2_def
    apply (subst qrhl_subst_right[symmetric])
    using \<open>bij \<tau>\<close> \<open>valid_var_subst \<tau>\<close> eq_def by auto
  also have "substp_bij \<tau>2 A = substp \<sigma>'2 A"
    using \<open>bij \<tau>2\<close> \<open>valid_var_subst \<tau>2\<close> \<tau>\<sigma>'2 substp_substp_bij by auto
  also have "substp_bij \<tau>2 B = substp \<sigma>'2 B"
    using \<open>bij \<tau>2\<close> \<open>valid_var_subst \<tau>2\<close> \<tau>\<sigma>'2 substp_substp_bij by auto
  also have "substp \<sigma>'2 A = substp \<sigma>2 A"
    by (rule substp_cong, auto)
  also have "substp \<sigma>'2 B = substp \<sigma>2 B"
    by (rule substp_cong, auto)
  also have "full_subst_vars \<tau> d =a= full_subst_vars \<tau> d'"
    using \<open>valid_var_subst \<tau>\<close> _ \<open>d =a= d'\<close> apply (rule alpha_eq_full_subst)
    using \<open>bij \<tau>\<close> bij_betw_imp_inj_on by blast
  also have "full_subst_vars \<tau> d' =d= full_subst_vars \<sigma>' d'"
    using \<open>valid_var_subst \<tau>\<close> \<tau>\<sigma>' full_subst_vars_cong by fastforce
  also have "full_subst_vars \<sigma>' d' = subst_vars \<sigma>' d'"
    (* Because all locals of d' are fresh *)
    apply (rule full_subst_vars_subst_vars_eq)
    using d'avoid by blast
  also have "subst_vars \<sigma>' d' = subst_vars \<sigma> d'"
    apply (rule subst_vars_cong, simp)
    using \<open>d =a= d'\<close> \<sigma>'_def fv_alpha by auto
  also have "subst_vars \<sigma> d' =a= subst_vars \<sigma> d"
    apply (rule subst_vars_alpha_eq)
    by (auto simp add: \<open>d =a= d'\<close> alpha_eq_sym)
  finally show ?thesis 
    by (simp add: eq_def)
qed


lemma rename_locals:
  fixes \<sigma> V
  assumes valid: "valid_var_subst \<sigma>"
  defines "W \<equiv> \<sigma> ` V"
  assumes inj: "inj_on \<sigma> V"
  assumes disj: "(fv c - V) \<inter> W = {}"
  assumes dom: "var_subst_dom \<sigma> \<subseteq> V"
  assumes [simp]: "finite V"
  assumes no: "no_conflict \<sigma> c"
  shows "locals V c =d= locals W (subst_vars \<sigma> c)"
proof -
  obtain V' where V_def: "V = set V'"
    using \<open>finite V\<close> finite_list by blast
  have "locals V c =d= foldr Local V' c"
    by (simp add: V_def locals.F_foldr)
  also have "\<dots> =d= foldr Local (map \<sigma> V') (subst_vars \<sigma> c)"
    apply (rule alpha_denot_eq)
    apply (rule rename_locals_alpha)
    using assms unfolding V_def W_def by auto
  also have "\<dots> =d= locals W (subst_vars \<sigma> c)"
    by (metis V_def W_def equivp_symp inits.equiv_R list.set_map locals.F_foldr)

  finally show ?thesis
    by -
qed

end
