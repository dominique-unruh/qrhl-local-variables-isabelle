section \<open>Adversary Rule\<close>

theory Adversary_Rule
  imports Helping_Lemmas
begin

locale adversary_rule =
  fixes s :: "nat \<Rightarrow> context" 
  fixes s' :: "nat \<Rightarrow> context"
  fixes R :: predicate
  fixes aux :: var
  fixes Rv defines "Rv \<equiv> deidx12 (fvp R)"
begin

definition "subst C = substitute C s"
definition "subst' C = substitute C s'"

lemma finite_Rv: "finite Rv"
  unfolding Rv_def deidx12_def apply simp
  unfolding vimage_def[symmetric] 
  by (meson finite_fvp finite_vimageI idx_inj injI)+

abbreviation "qrhlC V C \<equiv> qRHL (R \<sqinter> Eq V) (subst C) (subst' C) (R \<sqinter> Eq V)"

lemma context_induct[
    params     i and p and           e C1 C2 and   e C and   x C and                      q C and                     C1 C2, 
    case_names Hole program[program] IfTE[IH1 IH2] While[IH] LocalC[IH program classical] LocalQ[IH program quantum] Seq[IH1 IH2]]:
  fixes P :: "context \<Rightarrow> bool"
    and "context" :: "context"
  assumes "\<And>i. P (Hole i)"
    and "\<And>p. program p \<Longrightarrow> P p"
    and "\<And>e C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> P (IfTE e C1 C2)"
    and "\<And>e C. P C \<Longrightarrow> P (While e C)"
    and "\<And>x C. P C \<Longrightarrow> \<not> program C \<Longrightarrow> is_classical x \<Longrightarrow> P (Local x C)"
    and "\<And>q C. P C \<Longrightarrow> \<not> program C \<Longrightarrow> is_quantum q \<Longrightarrow> P (Local q C)"
    and "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> P (Seq C1 C2)"
  shows "P context"
  apply (rule context.induct)
  using assms apply (auto intro!: program.intros)
  by (meson program.intros(9))

lemma adversary_rule0:
  fixes V :: "var set"
  fixes Vmid :: "var set"
  assumes inf_aux: "infinite_var aux" 
  assumes quant_aux: "is_quantum aux"
  assumes aux_R: "aux \<notin> Rv"
  assumes aux_si: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s i)"
  assumes aux_s'i: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s' i)"
  assumes finite_Vmid: "finite Vmid"
  assumes qrhl_s: "\<And>i. i\<in>holes C \<Longrightarrow> qRHL (R \<sqinter> Eq Vmid) (s i) (s' i) (R \<sqinter> Eq Vmid)"
  assumes aux_Vmid: "aux \<in> Vmid"
  assumes Vmid_V: "Vmid \<supseteq> V \<union> inner C"
  assumes Vmid_R: "Vmid \<inter> Rv \<subseteq> V \<union> covered C"
  assumes Vmid_s: "\<And>i. i\<in>holes C \<Longrightarrow> Vmid \<inter> (fv (s i) \<union> fv (s' i)) \<subseteq> classical' (overwr (s i) \<inter> overwr (s' i)) \<union> covered C \<union> V"
  assumes fv_V: "fv C \<subseteq> V"
  assumes R_inner: "Rv \<inter> inner C = {}"
  assumes R_written: "Rv \<inter> written C = {}"
  shows "qrhlC V C"
  using aux_si aux_s'i finite_Vmid qrhl_s aux_Vmid Vmid_V Vmid_R Vmid_s fv_V R_inner R_written apply atomize
proof (induction C arbitrary: V Vmid rule:context_induct)
  case (program p)

  from program.prems
  have R_written: "Rv \<inter> written p = {}"
    by simp

  from \<open>fv p \<subseteq> V\<close>
  have "qRHL (Eq V) p p (Eq V)"
    by (rule equal_rule)
  then have "qRHL (R \<sqinter> Eq V) p p (R \<sqinter> Eq V)"
    unfolding inf.commute[of R]
    apply (rule frame_rule[rotated -1])
    using R_written \<open>program p\<close>
    by (auto simp add: Rv_def deidx12_def idx12_def is_classical'_def)
  then show ?case 
    by (simp add: program.program subst_def subst'_def substitute_program)
next
  case (Seq C1 C2)
  have subst: "subst (Seq C1 C2) = Seq (subst C1) (subst C2)"
    unfolding subst_def by simp
  have subst': "subst' (Seq C1 C2) = Seq (subst' C1) (subst' C2)"
    unfolding subst'_def by simp

  have "qrhlC V C1"
    apply (rule Seq.IH1)
    using Seq.prems by (auto simp: idx12_def)
  moreover have "qrhlC V C2"
    apply (rule Seq.IH2)
    using Seq.prems by (auto simp: idx12_def)
  ultimately show ?case
    unfolding subst subst'
    by (rule seq)
next
  case (IfTE e C1 C2)
  have subst: "subst (IfTE e C1 C2) = IfTE e (subst C1) (subst C2)"
    unfolding subst_def by simp
  have subst': "subst' (IfTE e C1 C2) = IfTE e (subst' C1) (subst' C2)"
    unfolding subst'_def by simp

  from IfTE.prems
  have "CVar ` fve e \<subseteq> V"
    by auto
  then have Eq_e: "Eq V \<le> Eq (CVar ` fve e)"
    apply (subst asm_rl[of "V = (CVar ` fve e) \<union> (V - CVar ` fve e)"], blast)
    apply (subst Eq_split)
    by (auto simp: is_classical'_def)

  have "qrhlC V C1"
    apply (rule IfTE.IH1)
    using IfTE.prems by (auto simp: idx12_def)   
  moreover have "qrhlC V C2"
    apply (rule IfTE.IH2)
    using IfTE.prems by (auto simp: idx12_def)
  ultimately show ?case
    unfolding subst subst'
    apply (rule joint_if_rule[rotated -2])
    using Eq_e by (simp_all add: inf.coboundedI2)
next
  case (While e C)
  have subst: "subst (While e C) = While e (subst C)"
    unfolding subst_def by simp
  have subst': "subst' (While e C) = While e (subst' C)"
    unfolding subst'_def by simp

  from While.prems
  have "CVar ` fve e \<subseteq> V"
    by simp
  then have Eq_e: "Eq V \<le> Eq (CVar ` fve e)"
    apply (subst asm_rl[of "V = (CVar ` fve e) \<union> (V - CVar ` fve e)"], blast)
    apply (subst Eq_split)
    by (auto simp: is_classical'_def)

  have "qrhlC V C"
    apply (rule While.IH)
    using While.prems apply simp
    using While.prems apply (auto simp: idx12_def)[1]
    using While.prems by auto
  then show ?case
    unfolding subst subst'
    apply (rule joint_while_rule[rotated 1])
    using Eq_e by (simp_all add: inf.coboundedI2)
next
  case (LocalC x C)
  have subst: "subst (Local x C) = Local x (subst C)"
    unfolding subst_def by simp
  have subst': "subst' (Local x C) = Local x (subst' C)"
    unfolding subst'_def by simp

  from LocalC.classical
  obtain x' where x': "x = CVar x'"
    using is_classical.cases by blast

  from LocalC.program
  have inner: "inner (Local x C) = {x} \<union> inner C"
    by simp
  moreover 
  from LocalC.prems
  have R_inner: "Rv \<inter> inner (Local x C) = {}"
    by simp
  ultimately have xR: " x \<notin> Rv"
    by auto

  have [simp]: "CVar (idxc b x') = idx b x" for b
    unfolding x' by simp

  have "qrhlC (insert x V) C"
    apply (rule LocalC.IH[where V="insert x V"])
    using LocalC.prems inner by (auto simp: idx12_def)
  then have "qrhlC (V-{x}) (Local x C)"
    unfolding subst subst'
    apply (rule_tac joint_local0_rule[rotated -1])
    using xR by (auto simp: Rv_def deidx12_def)
  then have "qRHL (R \<sqinter> Eq (V-{x}) \<sqinter> Eq (V\<inter>{x}))
             (subst (Local x C)) (subst' (Local x C))
             (R \<sqinter> Eq (V-{x}) \<sqinter> Eq (V\<inter>{x}))"
    apply (rule frame_rule[rotated -1])
    by (auto simp: is_classical'_def subst subst' idx12_def intro!: program.intros)
  then show ?case
    unfolding inf.assoc 
    unfolding inf.commute[of "Eq (V-{x})"]
    apply (subst (asm) Eq_split[symmetric], simp add: is_classical'_def LocalC.classical)
    apply (subst (asm) Eq_split[symmetric], simp add: is_classical'_def LocalC.classical)
    by (simp add: Un_Diff_Int Un_commute)
next
  case (LocalQ q C)

  from LocalQ.program
  have [simp]: "inner (Local q C) = insert q (inner C)"
    by simp

  from LocalQ.prems
  have [simp]: "finite V"
    using rev_finite_subset by blast

  have cofin: "\<exists>x. compatible q x \<and> P x" if "finite {x. \<not> P x}" for P :: "var \<Rightarrow> bool" and q
  proof -
    have "{x. compatible q x \<and> P x} = Collect (compatible q) - {x. \<not> P x}"
      by auto
    also have "infinite (Collect (compatible q) - {x. \<not> P x})"
      using that apply (rule Diff_infinite_finite)
      by (simp add: compatible_inexhaust)
    finally have "{x. compatible q x \<and> P x} \<noteq> {}"
      by force
    then show ?thesis
      by auto
  qed

  have [simp]: "finite {r. \<exists>i\<in>holes C. r \<in> fv (s i)}"
    apply (subst Collect_bex_eq)
    apply (rule finite_Union)
    by auto

  obtain r :: var where [simp]: \<open>compatible q r\<close>
    and "r \<notin> fv (subst C)"
    and "r \<notin> fv (subst' C)"
    and "r \<notin> Rv"
    and "r \<noteq> q"
    and "r \<notin> V"
    and [simp]: "\<And>i. i\<in>holes C \<Longrightarrow> r \<notin> fv (s i)"
    and [simp]: "\<And>i. i\<in>holes C \<Longrightarrow> r \<notin> fv (s' i)"
    apply atomize_elim
    apply (rule cofin)
    by (auto intro!: finite_Rv finite_vimageI[unfolded vimage_def, unfolded inj_on_def, rule_format])
  from \<open>compatible q r\<close> have [simp]: \<open>is_quantum r\<close>
    using LocalQ.quantum compatible_is_classical by blast

  from LocalQ.quantum \<open>is_quantum r\<close>
  obtain q' r' :: qvar where q': "q = QVar q'" and r': "r = QVar r'"
    by (metis (full_types) is_classical_CVar var.exhaust)
  with \<open>compatible q r\<close> have [simp]: \<open>compatible (QVar q') (QVar r')\<close>
    by simp

  define V' where
    "V' = (if q\<in>V then insert r V - {q} else V)"

  have "q \<notin> V'"
    unfolding V'_def by auto

  from LocalQ.prems
  have qR: "q \<notin> Rv"
    by simp

  have subst: "subst (Local q C) = Local q (subst C)"
    unfolding subst_def by simp
  have subst': "subst' (Local q C) = Local q (subst' C)"
    unfolding subst'_def by simp

  from LocalQ.prems
  have qrhl_s: "qRHL (R \<sqinter> Eq Vmid) (s i) (s' i) (R \<sqinter> Eq Vmid)" if "i\<in>holes C" for i
    using that by simp

  from LocalQ.prems
  have aux_si: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s i)" 
    and aux_s'i: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s' i)"
    by auto

  have qrhl_sr: "qRHL (R \<sqinter> Eq (insert r Vmid)) (s i) (s' i) (R \<sqinter> Eq (insert r Vmid))" 
    if "i\<in>holes C" for i
    apply (subst asm_rl[of "insert r Vmid = (Vmid-{aux}) \<union> {aux,r}"], 
               (auto simp add: \<open>aux \<in> Vmid\<close>)[1])+
    apply (rule varchange[where Q="{aux}" and q=aux, rotated -1])
          apply (subst asm_rl[of "Vmid - {aux} \<union> {aux} = Vmid"], (auto simp add: \<open>aux \<in> Vmid\<close>)[1])+
          using that apply (rule qrhl_s)
    using quant_aux \<open>is_quantum r\<close> inf_aux aux_R aux_si aux_s'i that
    by (auto simp add: is_quantum'_def Rv_def deidx12_def)

  have "qrhlC (insert q V') C"
  proof (rule LocalQ.IH[where Vmid = "insert r Vmid"])
    show "finite (insert r Vmid)"
      using LocalQ.prems by simp
    show "aux \<in> insert r Vmid"
      using LocalQ.prems by simp
    show "insert q V' \<union> inner C \<subseteq> insert r Vmid"
      using LocalQ.prems V'_def by auto
    show "insert r Vmid \<inter> Rv \<subseteq> insert q V' \<union> covered C"
      using LocalQ.prems \<open>r \<notin> Rv\<close>
      by (auto simp: idx12_diff V'_def)
    show "\<forall>i. i\<in>holes C \<longrightarrow> insert r Vmid \<inter> (fv (s i) \<union> fv (s' i))
        \<subseteq> classical' (overwr (s i) \<inter> overwr (s' i)) \<union> covered C \<union> insert q V'"
      using LocalQ.prems unfolding V'_def by auto
    show "fv C \<subseteq> insert q V'"
      using LocalQ.prems V'_def by auto
    show "Rv \<inter> inner C = {}"
      using LocalQ.prems by auto
    from LocalQ.prems
    have R_written: "Rv \<inter> written (Local q C) = {}"
      by simp
    then show "Rv \<inter> written C = {}"
      using qR by auto
  qed (auto simp add: qrhl_sr aux_si aux_s'i)

  then have qrhl_V': "qrhlC V' (Local q C)"
    unfolding subst subst'
    apply (rule joint_local0_rule[rotated -1])
    using qR \<open>q \<notin> V'\<close> \<open>q \<notin> V'\<close> by (auto simp: Rv_def deidx12_def)

  have [simp]: "QVar q' \<notin> fv (subst' (Local (QVar q') C))"
    using subst' by (simp add: q')
  have [simp]: "QVar r' \<notin> fv (subst' (Local (QVar q') C))"
    using \<open>r \<notin> fv (subst' C)\<close> subst' by (simp add: r' q')
  have [simp]: "QVar q' \<notin> fv (subst (Local (QVar q') C))"
    using subst by (simp add: q')
  have [simp]: "QVar r' \<notin> fv (subst (Local (QVar q') C))"
    using \<open>r \<notin> fv (subst C)\<close> subst by (simp add: r' q')
  have idx_r_R[simp]: "idx b r \<notin> fvp R" for b
    apply (cases b)
    using \<open>r \<notin> Rv\<close> by (simp_all add: r' deidx12_def Rv_def)
  have idx_q_R[simp]: "idx b q \<notin> fvp R" for b
    apply (cases b)
    using qR by (simp_all add: Rv_def deidx12_def)

  have swap_V': "transpose (QVar q') (QVar r') ` V' = V"
    unfolding V'_def
    using \<open>r \<noteq> q\<close> \<open>r \<notin> V\<close>
    by (auto simp: transpose_def q'[symmetric] r'[symmetric])

  have "R \<sqinter> Eq V
        = substp_bij (transpose (idx True q) (idx True r) o
                   (transpose (idx False q) (idx False r))) (R \<sqinter> Eq V')"
    apply (subst substp_bij_inter)
      apply (auto intro!: valid_var_subst_comp compatible_idx simp: bij_swap_iff)[2]
    apply (subst substp_bij_id)
       apply (auto intro!: valid_var_subst_comp compatible_idx simp: bij_swap_iff)[3]
     apply (metis idx_q_R idx_r_R transpose_apply_other)
    using substp_bij_Eq  q' r' apply auto
    by (metis \<open>compatible q r\<close> \<open>r \<noteq> q\<close> swap_V')
  also have \<open>\<dots> = substp (transpose (idx True q) (idx True r)) (substp (transpose (idx False q) (idx False r)) (R \<sqinter> Eq V'))\<close>
    apply (subst substp_bij_comp[symmetric])
        apply auto[4]
    apply (subst substp_substp_bij[where \<tau>=\<open>transpose (idx True q) (idx True r)\<close>])
       apply auto[3]
    apply (subst substp_substp_bij[where \<tau>=\<open>transpose (idx False q) (idx False r)\<close>])
    by auto

  also have "qRHL \<dots> (subst (Local q C)) (subst' (Local q C)) \<dots>"
    unfolding q' r'
    apply (rule rename_qrhl1)
      apply auto[3]
    apply (rule rename_qrhl2)
      apply auto[3]
    using q' qrhl_V' by blast

  finally show "qrhlC V (Local q C)"
    by simp
next
  case (Hole i)

  define X Y Q C where "X = {x\<in>Vmid-V. is_classical x \<and> x \<in> overwr (s i) \<and> x \<in> overwr (s' i)}" 
    and "Y = {x\<in>Vmid-V. is_classical x \<and> \<not> (x \<in> overwr (s i) \<and> x \<in> overwr (s' i))}"
    and "Q = {x\<in>Vmid-V. is_quantum x}" and [simp]: "C = Hole i"
  
  have quant_Q[simp]: "is_quantum' Q"
    unfolding is_quantum'_def Q_def by simp
  have class_Y[simp]: "is_classical' Y"
    using Y_def is_classical'_def by blast

  from \<open>aux \<in> Vmid\<close> quant_aux
  have [simp]: "aux \<in> V \<union> Q"
    by (simp add: Q_def)

  from Hole.prems
  have Vmid_s: "Vmid \<inter> (fv (s i) \<union> fv (s' i)) \<subseteq> classical' (overwr (s i) \<inter> overwr (s' i)) \<union> covered C \<union> V"
    and Vmid_R: "Vmid \<inter> Rv \<subseteq> V \<union> covered C"
    and Vmid_V: "V \<union> inner C \<subseteq> Vmid"
    and qrhl_s: "qRHL (R \<sqinter> Eq Vmid) (s i) (s' i) (R \<sqinter> Eq Vmid)"
    by simp_all

  from Vmid_s
  have sQ: "fv (s i) \<inter> Q = {}" and s'Q: "fv (s' i) \<inter> Q = {}"
    by (auto simp add: Q_def classical'_def)

  from \<open>finite Vmid\<close>
  have "finite X"
    unfolding X_def by simp

  have class_X: "is_classical' X"
    unfolding X_def is_classical'_def by simp

  from Vmid_s
  have X_overwr_si: "X \<subseteq> overwr (s i)" and X_overwr_si': "X \<subseteq> overwr (s' i)"
    using overwr_fv[of "s i"] overwr_fv[of "s' i"] unfolding X_def classical'_def by auto

  then obtain Xlist where Xlist: "X = CVar ` set Xlist"
    using class_X \<open>finite X\<close>
    by (metis finite_list is_classical'_def finite_subset_image imageI is_classical.simps subsetI)
  have Vmid_XYQ: "Vmid = V \<union> X \<union> Y \<union> Q"
    unfolding X_def Y_def Q_def using Vmid_V by blast
  have "X \<inter> V = {}" and "X \<inter> Y = {}" and "X \<inter> Q = {}"
    unfolding X_def Y_def Q_def
    by auto
  moreover 
  from \<open>X \<inter> V = {}\<close>
  have "idx12 X \<inter> idx12 V = {}"
    unfolding idx12_def by auto
  then have "idx12 X \<inter> fvp R = {}"
    using Vmid_R unfolding Rv_def deidx12_def idx12_def Vmid_XYQ idx12_union by auto
  ultimately have 1: "idx12 X \<inter> fvp (R \<sqinter> Eq (V \<union> Y \<union> Q)) = {}"
    apply (rule_tac fvp_inter_empty)
    by (auto simp add: idx12_def)

  have "Y \<inter> V = {}" and "Y \<inter> Q = {}"
    unfolding Y_def Q_def by auto
  moreover 
  from \<open>Y \<inter> V = {}\<close>
  have "idx12 Y \<inter> idx12 V = {}"
    unfolding idx12_def by auto
  then have "idx12 Y \<inter> fvp R = {}"
    using Vmid_R unfolding Rv_def idx12_def deidx12_def Vmid_XYQ idx12_union by auto
  ultimately have 2: "idx12 Y \<inter> fvp (R \<sqinter> Eq (V \<union> Q)) = {}"
    apply (rule_tac fvp_inter_empty)
    by (auto simp add: idx12_def)
  have siY: "fv (s i) \<inter> Y = {}" and s'iY: "fv (s' i) \<inter> Y = {}"
    using Vmid_s unfolding Y_def classical'_def by auto

  have "R \<sqinter> Eq (V \<union> Q) \<sqinter> Eq Y = R \<sqinter> Eq (V \<union> Y \<union> Q)"
    apply (subst asm_rl[of "V \<union> Y \<union> Q = Y \<union> (V \<union> Q)"], blast)
    apply (subst Eq_split[where X=Y], simp)
    by (simp add: inf_commute inf_left_commute)
  also have "qRHL (R \<sqinter> Eq (V \<union> Y \<union> Q)) (Assign Xlist some_constant) (Assign Xlist some_constant) (R \<sqinter> Eq Vmid)"
    apply (subst asm_rl[of "R \<sqinter> Eq Vmid = Eq (CVar ` set Xlist) \<sqinter> (R \<sqinter> Eq (V \<union> Y \<union> Q))"])
     apply (metis Eq_split Vmid_XYQ Xlist class_X inf_left_commute sup_commute sup_left_commute)
    apply (subst asm_rl[of "(R \<sqinter> Eq (V \<union> Y \<union> Q)) = top \<sqinter> (R \<sqinter> Eq (V \<union> Y \<union> Q))"], simp)
    apply (rule frame_rule)
    using 1 apply (auto simp: idx12_def Xlist[symmetric] intro!: program.intros) [2]
    by (rule assign_Eq)
  also from qrhl_s have "qrhlC Vmid C"
    unfolding subst_def subst'_def by auto
  also have "Assign Xlist some_constant; subst C =d= subst C"
    apply (rule denot_eq_init)
    unfolding subst_def apply auto using X_overwr_si Xlist by blast
  also have "Assign Xlist some_constant; subst' C =d= subst' C"
    apply (rule denot_eq_init)
    unfolding subst'_def apply auto using X_overwr_si' Xlist by blast
  also have "R \<sqinter> Eq Vmid \<le> R \<sqinter> Eq (V \<union> Q)"
    apply (rule inf_mono, simp)
    apply (rule weaken_Eq)
    using class_X Vmid_XYQ is_classical'_def Q_def
    by blast+
  finally have "qRHL (R \<sqinter> Eq (V \<union> Q) \<sqinter> Eq Y) (subst C) (subst' C) (R \<sqinter> Eq (V \<union> Q))"
    by auto

  then have qrhl_VQ: "qrhlC (V \<union> Q) C"
    apply (rule drop_Eq[rotated -1]) 
    using 2 siY s'iY by (auto simp: subst_def subst'_def)

  from Hole.prems
  have aux_si: "aux \<notin> fv (s i)"
    and aux_s'i: "aux \<notin> fv (s' i)"
    by auto

  have "qrhlC ((V - {aux}) \<union> (V \<inter> {aux})) (Hole i)"
    apply (rule varchange[where Q="insert aux Q" and q=aux])
    using inf_aux quant_aux quant_Q aux_R
      aux_si aux_s'i sQ s'Q
          apply (auto simp: is_quantum'_def idx12_def subst_def subst'_def Rv_def deidx12_def)[6]
    using qrhl_VQ \<open>aux \<in> V \<union> Q\<close>
    by (metis C_def Un_insert_right insert_Diff_single insert_absorb sup_commute)

  then show ?case
    by (simp add: Un_Diff_Int)
qed

lemma adversary_rule:
  fixes Vin :: "var set"
  fixes Vout :: "var set"
  fixes Vmid :: "var set"
  assumes inf_aux: "infinite_var aux" 
  assumes quant_aux: "is_quantum aux"
  assumes aux_R: "aux \<notin> Rv"
  assumes finite_Vmid: "finite Vmid"
  assumes finite_Vin: "finite Vin"
  assumes aux_si: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s i)"
  assumes aux_s'i: "\<And>i. i \<in> holes C \<Longrightarrow> aux \<notin> fv (s' i)"
  assumes qrhl_s: "\<And>i. i \<in> holes C \<Longrightarrow> qRHL (R \<sqinter> Eq Vmid) (s i) (s' i) (R \<sqinter> Eq Vmid)"
  assumes aux_Vmid: "aux \<in> Vmid"
  assumes inner_Vmid: "inner C \<subseteq> Vmid"
  assumes Vout_Vmid: "Vout \<subseteq> Vmid"
  assumes Vout_overwr_Vin: "Vout - overwr C \<subseteq> Vin"
  assumes Vout_Vin_R: "(Vout - Vin) \<inter> Rv = {}"
  assumes Vin_Vout_overwr: "quantum' Vin \<subseteq> Vout \<union> overwr C"
  assumes Vin_Vout_R: "quantum' (Vin - Vout) \<inter> Rv = {}"
  assumes Vmid_R_Vin_covered: "Vmid \<inter> Rv \<subseteq> Vin \<union> covered C"
  assumes Vmid_R_Vout_covered: "quantum' (Vmid \<inter> Rv) \<subseteq> Vout \<union> covered C"
  assumes Vmid_s_Vin_covered: "\<And>i. i \<in> holes C \<Longrightarrow> Vmid \<inter> (fv (s i) \<union> fv (s' i)) \<subseteq> Vin \<union> covered C \<union> classical' (overwr (s i) \<inter> overwr (s' i))"
  assumes Vmid_s_Vout_covered: "\<And>i. i \<in> holes C \<Longrightarrow> quantum' Vmid \<inter> (fv (s i) \<union> fv (s' i)) \<subseteq> Vout \<union> covered C"
  assumes C_Vmid: "fv C \<subseteq> Vmid"
  assumes C_Vin_overwr: "fv C \<subseteq> Vin \<union> overwr C"
  assumes C_Vin_R: "fv C \<inter> Rv \<subseteq> Vin"
  assumes C_Vout: "quantum' (fv C) \<subseteq> Vout"
  assumes R_inner: "Rv \<inter> inner C = {}"
  assumes R_written: "Rv \<inter> written C = {}"

  shows "qRHL (R \<sqinter> Eq Vin) (subst C) (subst' C) (R \<sqinter> Eq Vout)"
proof -
  define V where 
    "V = Vmid \<inter> (overwr C \<union> Vin) \<inter> (Vin \<union> - Rv) \<inter> (Vout \<union> range CVar)"

  have [simp]: "finite V"
    unfolding V_def
    using finite_Vmid by blast

  have Vmid_V: "V \<union> inner C \<subseteq> Vmid"
    unfolding V_def using inner_Vmid by auto
  have Vmid_R: "Vmid \<inter> Rv \<subseteq> V \<union> covered C"
    unfolding V_def
    using Vmid_R_Vin_covered Vmid_R_Vout_covered
    unfolding quantum'_def is_classical.simps
    by auto
  have Vmid_s: "Vmid \<inter> (fv (s i) \<union> fv (s' i))
         \<subseteq> classical' (overwr (s i) \<inter> overwr (s' i)) \<union> covered C \<union> V" if "i\<in>holes C" for i
    unfolding V_def Un_Int_distrib
    apply (rule Int_greatest)+
       apply blast
      using Vmid_s_Vin_covered that apply blast
     using Vmid_s_Vin_covered that apply fastforce
    using Vmid_s_Vout_covered that by (auto simp: quantum'_def is_classical.simps)
  have fv_V: "fv C \<subseteq> V"
    using C_Vmid C_Vin_overwr C_Vin_R C_Vout
    unfolding V_def Rv_def quantum'_def is_classical.simps by auto
  have V_Vin_overwr: "V - Vin \<subseteq> overwr C"
    unfolding V_def by auto
  have Vin_V_overwr: "quantum' (Vin - V) \<subseteq> overwr C"
    using Vout_Vmid Vin_Vout_overwr
    unfolding V_def quantum'_def
    by auto
  have V_Vin_R: "idx12 (V - Vin) \<inter> fvp R = {}"
    unfolding V_def idx12_def deidx12_def Rv_def by auto
  have "quantum' (Vin - V) \<inter> deidx12 (fvp R) = {}"
    using Vin_Vout_R Diff_disjoint Vout_Vmid 
    unfolding V_def quantum'_def Rv_def
    by auto
  then have Vin_V_R: "idx12 (quantum' (Vin - V)) \<inter> fvp R = {}"
    unfolding deidx12_def idx12_def by auto
  have Vout_V: "Vout \<subseteq> V"
    using Vout_Vmid Vout_overwr_Vin Vout_Vin_R 
    unfolding deidx12_def V_def Rv_def
    by auto
  have Vout_V_class: "is_classical' (V - Vout)"
    unfolding V_def is_classical'_def by auto

  from inf_aux quant_aux aux_R aux_si aux_s'i  finite_Vmid qrhl_s aux_Vmid Vmid_V Vmid_R Vmid_s fv_V R_inner R_written
  have \<open>qrhlC V C\<close>
    by (rule adversary_rule0[where Vmid=Vmid])

  then have \<open>qRHL (R \<sqinter> Eq Vin) (subst C) (subst' C) (R \<sqinter> Eq V)\<close>
    apply (rule change_Eq_precondition[rotated -1])
    using V_Vin_overwr overwr_subst subst'_def subst_def apply auto[1]
    using Vin_V_overwr overwr_subst subst'_def subst_def apply auto[1] 
    using \<open>finite V\<close> \<open>finite Vin\<close> V_Vin_R Vin_V_R by simp_all
  also have "R \<sqinter> Eq V \<le> R \<sqinter> Eq Vout"
    apply (rule inf_mono, simp)
    apply (subst asm_rl[of "V = (V-Vout) \<union> Vout"])
    using Vout_V apply auto[1]
    apply (subst Eq_split)
    using Vout_V_class by auto
  finally show ?thesis
    by auto 

qed

end

end
