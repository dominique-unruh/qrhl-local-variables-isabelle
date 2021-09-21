section \<open>Assumptions\<close>

theory Assumptions
  imports Basic_Definitions
begin

axiomatization where
  compatible_trans[trans]: "compatible x y \<Longrightarrow> compatible y z \<Longrightarrow> compatible x z"
and compatible_sym[sym]: "compatible x y \<Longrightarrow> compatible y x"
and compatible_inexhaust: "infinite {x'. compatible x x'}"

axiomatization where 
  compatible_is_classical: "compatible x y \<Longrightarrow> is_classical x \<longleftrightarrow> is_classical y"


axiomatization where
  seq0: "program p1 \<Longrightarrow> program p2 \<Longrightarrow> qrhl A p1 p2 B \<Longrightarrow> qrhl B p1' p2' C \<Longrightarrow> qrhl A (p1; p1') (p2; p2') C"


axiomatization where
  conseq_post0: "program p1 \<Longrightarrow> program p2 \<Longrightarrow> qrhl A p1 p2 B \<Longrightarrow> B \<le> C \<Longrightarrow> qrhl A p1 p2 C"


axiomatization where
  weaken_Eq: "V \<subseteq> W \<Longrightarrow> (\<And>x. x \<in> W - V \<Longrightarrow> is_classical x) \<Longrightarrow> Eq V \<ge> Eq W"

axiomatization where
  denot_eq_seq_assoc0: "program c \<Longrightarrow> program d \<Longrightarrow> program e \<Longrightarrow> denot_eq ((c; d); e) (c; (d; e))"

axiomatization where
  denot_eq_while_cong0: "program c \<Longrightarrow> program d \<Longrightarrow>denot_eq c d \<Longrightarrow> denot_eq (While e c) (While e d)"

axiomatization where
  denot_eq_seq_cong10: "program c \<Longrightarrow> program d \<Longrightarrow> program e \<Longrightarrow> denot_eq c d \<Longrightarrow> denot_eq (c; e) (d; e)"

axiomatization where
  denot_eq_seq_cong20: "program c \<Longrightarrow> program d \<Longrightarrow> program e \<Longrightarrow> denot_eq c d \<Longrightarrow> denot_eq (e; c) (e; d)"

axiomatization where
  denot_eq_ifte_cong10: "program c \<Longrightarrow> program d \<Longrightarrow> program e \<Longrightarrow> denot_eq c d \<Longrightarrow> denot_eq (IfTE f c e) (IfTE f d e)"

axiomatization where
  denot_eq_ifte_cong20: "program c \<Longrightarrow> program d \<Longrightarrow> program e \<Longrightarrow> denot_eq c d \<Longrightarrow> denot_eq (IfTE f e c) (IfTE f e d)"

axiomatization where
  denot_eq_qrhl_left0: "program p1 \<Longrightarrow> program p1' \<Longrightarrow> program p2 \<Longrightarrow> denot_eq p1 p1' \<Longrightarrow> qrhl A p1 p2 B \<longleftrightarrow> qrhl A p1' p2 B"

axiomatization where
  denot_eq_qrhl_right0: "program p1 \<Longrightarrow> program p2 \<Longrightarrow> program p2' \<Longrightarrow> denot_eq p2 p2' \<Longrightarrow> qrhl A p1 p2 B \<longleftrightarrow> qrhl A p1 p2' B"

axiomatization where
  denot_eq_init0: "program p \<Longrightarrow> CVar ` set X \<subseteq> overwr p \<Longrightarrow> denot_eq (Assign X some_constant; p) p"

axiomatization where
  denot_eq_qinit0: "program p \<Longrightarrow> distinct Q \<Longrightarrow> QVar ` set Q \<subseteq> overwr p \<Longrightarrow> denot_eq (QInit Q some_constant; p) p"

axiomatization where
  assign_Eq0: "qrhl top (Assign X some_constant) (Assign X some_constant) (Eq (CVar ` set X))"

axiomatization where
  qinit_Eq0: "distinct Q \<Longrightarrow> qrhl top (QInit Q some_constant) (QInit Q some_constant) (Eq (QVar ` set Q))"

axiomatization where
  Eq_split: "is_classical' X \<Longrightarrow> Eq (X \<union> Y) = Eq X \<sqinter> Eq Y"

axiomatization where
  Eq_split_leq: "V \<inter> W = {} \<Longrightarrow> Eq V \<sqinter> Eq W \<le> Eq (V \<union> W)"

axiomatization where
  frame_rule0: "program c \<Longrightarrow> program d \<Longrightarrow> (idx True ` written c) \<inter> fvp R = {}
     \<Longrightarrow> (idx False ` written d) \<inter> fvp R = {} \<Longrightarrow> qrhl A c d B
     \<Longrightarrow> qrhl (A \<sqinter> R) c d (B \<sqinter> R)"

axiomatization where
  fvp_Eq[simp]: "fvp (Eq V) = idx12 V"

axiomatization where
  fvp_inter: "fvp (A \<sqinter> B) \<subseteq> fvp A \<union> fvp B"

axiomatization where
  varchange0: "program c \<Longrightarrow> program d \<Longrightarrow> is_quantum' Q \<Longrightarrow> is_quantum' Q' \<Longrightarrow> q \<in> Q
     \<Longrightarrow> infinite_var q \<Longrightarrow> (fvp A \<union> fvp B) \<inter> (idx12 Q \<inter> idx12 Q') = {} 
     \<Longrightarrow> (fv c \<union> fv d) \<inter> (Q \<union> Q') = {} \<Longrightarrow> qrhl (A \<sqinter> Eq (Vl \<union> Q)) c d (B \<sqinter> Eq (Vr \<union> Q))
     \<Longrightarrow> qrhl (A \<sqinter> Eq (Vl \<union> Q')) c d (B \<sqinter> Eq (Vr \<union> Q'))"

axiomatization where
  drop_Eq0: "program c \<Longrightarrow> program d \<Longrightarrow> is_classical' X \<Longrightarrow> fvp A \<inter> idx12 X = {}
      \<Longrightarrow> fv c \<inter> X = {} \<Longrightarrow> fv d \<inter> X = {} \<Longrightarrow> qrhl (A \<sqinter> Eq X) c d B \<Longrightarrow> qrhl A c d B"

axiomatization where
  equal_rule0: "program p \<Longrightarrow> fv p \<subseteq> V \<Longrightarrow> qrhl (Eq V) p p (Eq V)"

axiomatization where
    \<comment> \<open>Weakened w.r.t. original\<close>
  joint_while_rule0: "program c \<Longrightarrow> program d \<Longrightarrow> A \<le> Eq (CVar ` fve e) \<Longrightarrow> qrhl A c d A \<Longrightarrow> qrhl A (While e c) (While e d) A"

axiomatization where
    \<comment> \<open>Weakened w.r.t. original\<close>
  joint_if_rule0: "program c1 \<Longrightarrow> program d1 \<Longrightarrow> program c2 \<Longrightarrow> program d2 \<Longrightarrow> A \<le> Eq (CVar ` fve e) \<Longrightarrow> qrhl A c1 c2 B \<Longrightarrow> qrhl A d1 d2 B \<Longrightarrow> qrhl A (IfTE e c1 d1) (IfTE e c2 d2) A"

(* Rule JointRemoveLocal0 *)
axiomatization where
  joint_local0_rule0: "program c \<Longrightarrow> program d 
    \<Longrightarrow> idx True v \<notin> fvp A \<Longrightarrow> idx False v \<notin> fvp A \<Longrightarrow> v \<notin> S \<Longrightarrow> v \<notin> R 
    \<Longrightarrow> qrhl (A \<sqinter> Eq (insert v S)) c d (A \<sqinter> Eq (insert v R))
    \<Longrightarrow> qrhl (A \<sqinter> Eq S) (Local v c) (Local v d) (A \<sqinter> Eq R)"

axiomatization where
  rename_qrhl10: "program c \<Longrightarrow> program d \<Longrightarrow> QVar q \<notin> fv c 
    \<Longrightarrow> QVar r \<notin> fv c \<Longrightarrow> qrhl A c d B 
    \<Longrightarrow> qrhl (rename_predicate A (idxq True q) (idxq True r)) c d 
             (rename_predicate B (idxq True q) (idxq True r))"

axiomatization where
  rename_qrhl20: "program c \<Longrightarrow> program d \<Longrightarrow> QVar q \<notin> fv d
     \<Longrightarrow> QVar r \<notin> fv d \<Longrightarrow> qrhl A c d B 
     \<Longrightarrow> qrhl (rename_predicate A (idxq False q) (idxq False r)) c d 
              (rename_predicate B (idxq False q) (idxq False r))"

axiomatization where
  joint_init_eq00: "QVar ` set Q \<subseteq> V \<Longrightarrow> is_quantum' V \<Longrightarrow> qrhl (Eq V) 
        (QInit Q some_constant) (QInit Q some_constant)
        (Eq (V - QVar ` set Q))"

axiomatization where
  seq_c_skip0[simp]: "program c \<Longrightarrow> denot_eq (c; Skip) c"

axiomatization where
  seq_skip_c0[simp]: "program c \<Longrightarrow> denot_eq (Skip; c) c"

axiomatization where
  local_idem0[simp]: "program C \<Longrightarrow> denot_eq (Local x (Local x C)) (Local x C)"


text \<open>\lautoeqref{hgdfaysdgfyasdgfasdfh}{lemma:local.swap}\<close>
axiomatization where
  local_swap0: "program C \<Longrightarrow> denot_eq (Local x (Local y C)) (Local y (Local x C))"

(* lemma:merge.local *)
axiomatization where
  local_seq_merge0: "program c1 \<Longrightarrow> program c2 \<Longrightarrow> denot_eq (Local x c1; Local x c2) (Local x (c1; init x; c2))"

(* lemma:swap *)
axiomatization where
  swap0: "program c \<Longrightarrow> program d \<Longrightarrow> fv c \<inter> fv d = {} \<Longrightarrow> denot_eq (c;d) (d;c)"

(* lemma:unused *)
axiomatization where
  local_unused0: "program C \<Longrightarrow> x \<notin> fv C \<Longrightarrow> denot_eq (Local x C) C"

(* lemma:add.init.end *)
axiomatization where
  local_init_end0: "program c \<Longrightarrow> denot_eq (Local x (c; init x)) (Local x c)"

(* lemma:add.init.begin *)
axiomatization where
  local_init_beginning0: "program c \<Longrightarrow> denot_eq (Local x c) (Local x (init x; c))"

axiomatization where subst_vars_e_compose[simp]:
  "valid_var_subst \<tau> \<Longrightarrow> subst_vars_e \<sigma> (subst_vars_e \<tau> e) = subst_vars_e (\<sigma> o \<tau>) e"

axiomatization where subst_vars_e_cong:
  "valid_var_subst \<sigma> \<Longrightarrow> (\<And>x. x\<in>CVar ` fve e \<Longrightarrow> \<sigma> x = \<tau> x)
      \<Longrightarrow> subst_vars_e \<sigma> e = subst_vars_e \<tau> e"

(* TODO prove in paper *)
axiomatization where 
  full_subst_vars_denot_eq: "program c \<Longrightarrow> program d \<Longrightarrow> bij \<sigma> 
    \<Longrightarrow> valid_var_subst \<sigma> \<Longrightarrow> denot_eq (full_subst_vars \<sigma> c) (full_subst_vars \<sigma> d)"

(* lemma:full_subst_vars *)
(* TODO: should be provable from full_subst_vars_denot_eq *)
axiomatization where
  full_subst_vars_id0: "program c \<Longrightarrow> bij \<sigma> \<Longrightarrow> valid_var_subst \<sigma> \<Longrightarrow> var_subst_dom \<sigma> \<inter> fv c = {}
        \<Longrightarrow> denot_eq (full_subst_vars \<sigma> c) c"

axiomatization where subst_vars_e_id[simp]: "subst_vars_e (\<lambda>x. x) e = e"

axiomatization where fve_subst_vars_e[simp]:
  "valid_var_subst \<sigma> \<Longrightarrow> CVar ` fve (subst_vars_e \<sigma> e) = \<sigma> ` CVar ` fve e"

axiomatization where qrhl_subst_left0:
  "bij \<tau> \<Longrightarrow> valid_var_subst \<tau> \<Longrightarrow> program c \<Longrightarrow> program d \<Longrightarrow> qrhl A c d B \<Longrightarrow>
   qrhl (substp_bij (idx_var_subst True \<tau>) A) (full_subst_vars \<tau> c) d (substp_bij (idx_var_subst True \<tau>) B)"

axiomatization where qrhl_subst_right0:
  "bij \<tau> \<Longrightarrow> valid_var_subst \<tau> \<Longrightarrow> program c \<Longrightarrow> program d \<Longrightarrow> qrhl A c d B \<Longrightarrow>
   qrhl (substp_bij (idx_var_subst False \<tau>) A) c (full_subst_vars \<tau> d) (substp_bij (idx_var_subst False \<tau>) B)"

axiomatization where compatible_idx:
  "compatible v (idx side v)"

end
