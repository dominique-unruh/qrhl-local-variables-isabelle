section \<open>Basic Definitions\<close>

theory Basic_Definitions
  imports Main
begin

text \<open>Enabling infix notation for (binary) infimums.\<close>
notation inf (infixl "\<sqinter>" 70)

subsection "Variables"

typedecl qvar
axiomatization where infinite_qvar: "infinite (UNIV::qvar set)"

(* True = left, False = right *)
axiomatization idxq :: "bool \<Rightarrow> qvar \<Rightarrow> qvar" where
  idxq_inj[simp]: "idxq b q = idxq b' q' \<longleftrightarrow> b=b' \<and> q=q'"
typedecl cvar
axiomatization idxc :: "bool \<Rightarrow> cvar \<Rightarrow> cvar" where
  idxc_inj[simp]: "idxc b x = idxc b' x' \<longleftrightarrow> b=b' \<and> x=x'"

datatype var = QVar qvar | CVar cvar

fun idx :: "bool \<Rightarrow> var \<Rightarrow> var" where
  "idx b (QVar q) = QVar (idxq b q)"
| "idx b (CVar q) = CVar (idxc b q)"

definition "idx12 V = idx True ` V \<union> idx False ` V"
definition "deidx12 V = {x. idx True x \<in> V \<or> idx False x \<in> V}"
definition "deidx side V = {x. idx side x \<in> V}"
abbreviation "deidx1 \<equiv> deidx True"
abbreviation "deidx2 \<equiv> deidx False"

inductive is_classical where
  is_classical_CVar[simp]: "is_classical (CVar _)"
abbreviation "is_quantum x == \<not> is_classical x"

definition "is_classical' X \<longleftrightarrow> (\<forall>x\<in>X. is_classical x)"
definition "is_quantum' X \<longleftrightarrow> (\<forall>x\<in>X. is_quantum x)"

definition "classical' vs = {c\<in>vs. is_classical c}"
definition "quantum' vs = {q\<in>vs. is_quantum q}"

axiomatization infinite_var :: "var \<Rightarrow> bool"

axiomatization compatible :: "var \<Rightarrow> var \<Rightarrow> bool"
\<comment> \<open>\<^term>\<open>compatible x y\<close> means that \<^term>\<open>x\<close> and \<^term>\<open>y\<close> have the same type
    and are both classical or both quantum\<close>

subsection "Expressions"

typedecl expression

axiomatization fve :: "expression \<Rightarrow> cvar set" where
  finite_fve[simp]: "finite (fve e)"
and ex_constant: "\<exists>e. fve e = {}"

definition "some_constant = (SOME e. fve e = {})"

subsection "Contexts"

datatype "context" = 
  Hole nat | Assign "cvar list" expression | Sample "cvar list" expression | Skip
| QInit "qvar list" expression | QApply "qvar list" expression
| Measure "cvar list" "qvar list" expression
| IfTE expression "context" "context" | While expression "context"
| Local var "context" 
| Seq "context" "context" (infixl ";" 60)

inductive program :: "context \<Rightarrow> bool" where
  "program (Assign cv e)"
| "program (Sample cv e)"
| "program Skip"
| "program (QInit qv e)"
| "program (QApply qv e)"
| "program (Measure cv qv e)"
| "program p1 \<Longrightarrow> program p2 \<Longrightarrow> program (IfTE e p1 p2)"
| "program p \<Longrightarrow> program (While e p)"
| "program p ==> program (Local v p)"
| "program p1 \<Longrightarrow> program p2 \<Longrightarrow> program (Seq p1 p2)"


fun holes :: "context \<Rightarrow> nat set" where
  "holes (Hole i) = {i}"
| "holes (C1; C2) = holes C1 \<union> holes C2"
| "holes (IfTE e C1 C2) = holes C1 \<union> holes C2"
| "holes (While e C) = holes C"
| "holes (Local x C) = holes C"
| "holes _ = {}"

fun substitute :: "context \<Rightarrow> (nat \<Rightarrow> context) \<Rightarrow> context" where
  "substitute Skip _ = Skip"
| "substitute (Hole i) s = s i"
| "substitute (Seq C1 C2) s = Seq (substitute C1 s) (substitute C2 s)"
| "substitute (IfTE e C1 C2) s = IfTE e (substitute C1 s) (substitute C2 s)"
| "substitute (While e C) s = While e (substitute C s)"
| "substitute (Local V C) s = Local V (substitute C s)"
| "substitute p s = p"

fun block :: "context list \<Rightarrow> context" where
  "block [] = Skip"
| "block (c#cs) = Seq c (block cs)"

fun init :: "var \<Rightarrow> context" where
  "init (QVar q) = QInit [q] some_constant"
| "init (CVar c) = Assign [c] some_constant"

text \<open>A form inits of \<^term>\<open>init\<close> that initializes several variables is
defined in theory \<open>Helping_Lemmas\<close>\<close>


subsection "Variable sets"

fun fv :: "context \<Rightarrow> var set" where
  "fv (Hole i) = {}"
| "fv (Assign X e) = CVar ` (set X \<union> fve e)"
| "fv (Sample X e) = CVar ` (set X \<union> fve e)"
| "fv (Local x C) = fv C - {x}"
| "fv (QInit Q e) = QVar ` set Q \<union> CVar ` fve e"
| "fv (QApply Q e) = QVar ` set Q \<union> CVar ` fve e"
| "fv (Measure X Q e) = QVar ` set Q \<union> CVar ` (set X \<union> fve e)"
| "fv (Seq C1 C2) = fv C1 \<union> fv C2"
| "fv (IfTE e C1 C2) = CVar ` fve e \<union> fv C1 \<union> fv C2"
| "fv (While e C) = CVar ` fve e \<union> fv C"
| "fv Skip = {}"
for i :: nat and X :: "cvar list"

fun vars :: "context \<Rightarrow> var set" where
  "vars (Hole i) = {}"
| "vars (Assign X e) = CVar ` (set X \<union> fve e)"
| "vars (Sample X e) = CVar ` (set X \<union> fve e)"
| "vars (Local x C) = insert x (vars C)"
| "vars (QInit Q e) = QVar ` set Q \<union> CVar ` fve e"
| "vars (QApply Q e) = QVar ` set Q \<union> CVar ` fve e"
| "vars (Measure X Q e) = QVar ` set Q \<union> CVar ` (set X \<union> fve e)"
| "vars (Seq C1 C2) = vars C1 \<union> vars C2"
| "vars (IfTE e C1 C2) = CVar ` fve e \<union> vars C1 \<union> vars C2"
| "vars (While e C) = CVar ` fve e \<union> vars C"
| "vars Skip = {}"
for i :: nat and X :: "cvar list"

function inner :: "context \<Rightarrow> var set" where
  "inner (Hole i) = {}"
| "inner (Assign _ _) = {}"
| "inner (Sample _ _) = {}"
| "inner (QInit _ _) = {}"
| "inner (QApply _ _) = {}"
| "inner (Measure _ _ _) = {}"
| "inner (IfTE _ p1 p2) = inner p1 \<union> inner p2"
| "inner (While _ p) = inner p"
| "inner Skip = {}"
| "inner (Seq p1 p2) = inner p1 \<union> inner p2"
| "program p \<Longrightarrow> inner (Local v p) = {}"
| "\<not> program p \<Longrightarrow> inner (Local v p) = insert v (inner p)"
                      apply auto
  apply atomize_elim
  apply (case_tac x)
  by auto

termination by lexicographic_order

fun covered :: "context \<Rightarrow> var set" where
  "covered (Seq C1 C2) = covered C1 \<inter> covered C2"
| "covered (IfTE e C1 C2) = covered C1 \<inter> covered C2"
| "covered (While e C) = covered C"
| "covered (Local v C) = insert v (covered C)"
| "covered (Hole i) = {}"
| "covered C = UNIV"

fun overwr :: "context \<Rightarrow> var set" where
  "overwr (Hole i) = {}"
| "overwr (Assign X e) = CVar ` (set X - fve e)"
| "overwr (Sample X e) = CVar ` (set X - fve e)"
| "overwr (QInit Q e) = QVar ` set Q"
| "overwr (QApply Q e) = {}"
| "overwr (Measure X Q e) = CVar ` (set X - fve e)"
| "overwr (IfTE e C1 C2) = (overwr C1 \<inter> overwr C2) - CVar ` fve e"
| "overwr (While e C) = {}"
| "overwr (Local v C) = overwr C - {v}"
| "overwr (Seq C1 C2) = overwr C1 \<union> ((overwr C2 - fv C1) \<inter> covered C1)"
| "overwr Skip = {}"


fun written :: "context \<Rightarrow> var set" where
  "written (Hole i) = {}"
| "written (Assign X e) = CVar ` set X"
| "written (Sample X e) = CVar ` set X"
| "written (Local v C) = written C - {v}"
| "written (QInit Q e) = QVar ` set Q"
| "written (QApply Q e) = QVar ` set Q"
| "written (Measure X Q e) = QVar ` set Q \<union> CVar ` set X"
| "written (IfTE e C1 C2) = written C1 \<union> written C2"
| "written (While e C) = written C"
| "written Skip = {}"
| "written (Seq C1 C2) = written C1 \<union> written C2"


fun localvars :: "context \<Rightarrow> var set" where
  "localvars (Hole i) = {}"
| "localvars (Assign _ _) = {}"
| "localvars (Sample _ _) = {}"
| "localvars (QInit _ _) = {}"
| "localvars (QApply _ _) = {}"
| "localvars (Measure _ _ _) = {}"
| "localvars (IfTE _ p1 p2) = localvars p1 \<union> localvars p2"
| "localvars (While _ p) = localvars p"
| "localvars Skip = {}"
| "localvars (Seq p1 p2) = localvars p1 \<union> localvars p2"
| "localvars (Local v p) = insert v (localvars p)"

subsection \<open>Variable Substitutions\<close>

axiomatization subst_vars_e :: "(var\<Rightarrow>var) \<Rightarrow> expression \<Rightarrow> expression"

definition "valid_var_subst \<sigma> \<longleftrightarrow> (\<forall>x. compatible x (\<sigma> x))"

definition subst_vars_c :: "(var\<Rightarrow>var) \<Rightarrow> cvar \<Rightarrow> cvar" where
  "subst_vars_c \<sigma> c = (case \<sigma> (CVar c) of CVar c' \<Rightarrow> c')"
definition subst_vars_q :: "(var\<Rightarrow>var) \<Rightarrow> qvar \<Rightarrow> qvar" where
  "subst_vars_q \<sigma> q = (case \<sigma> (QVar q) of QVar q' \<Rightarrow> q')"

definition "var_subst_dom \<sigma> = {x. \<sigma> x \<noteq> x}"

definition "idx_var_subst side \<sigma> v
  = (if v \<in> range (idx side) then idx side (\<sigma> (inv (idx side) v)) else v)"

fun subst_vars :: "(var\<Rightarrow>var) \<Rightarrow> context \<Rightarrow> context" where
  "subst_vars _ (Hole i) = Hole i"
| "subst_vars _ Skip = Skip"
| "subst_vars \<sigma> (Assign X e) = Assign (map (subst_vars_c \<sigma>) X) (subst_vars_e \<sigma> e)"
| "subst_vars \<sigma> (Sample X e) = Sample (map (subst_vars_c \<sigma>) X) (subst_vars_e \<sigma> e)"
| "subst_vars \<sigma> (QInit Q e) = QInit (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "subst_vars \<sigma> (QApply Q e) = QApply (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "subst_vars \<sigma> (Measure X Q e) = Measure (map (subst_vars_c \<sigma>) X) (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "subst_vars \<sigma> (C1; C2) = subst_vars \<sigma> C1; subst_vars \<sigma> C2"
| "subst_vars \<sigma> (IfTE e C1 C2) = IfTE (subst_vars_e \<sigma> e) (subst_vars \<sigma> C1) (subst_vars \<sigma> C2)"
| "subst_vars \<sigma> (While e C) = While (subst_vars_e \<sigma> e) (subst_vars \<sigma> C)"
| "subst_vars \<sigma> (Local x C) = Local x (subst_vars (\<sigma>(x:=x)) C)"

fun full_subst_vars :: "(var\<Rightarrow>var) \<Rightarrow> context \<Rightarrow> context" where
  "full_subst_vars \<sigma> (Hole i) = Hole i"
| "full_subst_vars \<sigma> Skip = Skip"
| "full_subst_vars \<sigma> (Assign X e) = Assign (map (subst_vars_c \<sigma>) X) (subst_vars_e \<sigma> e)"
| "full_subst_vars \<sigma> (Sample X e) = Sample (map (subst_vars_c \<sigma>) X) (subst_vars_e \<sigma> e)"
| "full_subst_vars \<sigma> (QInit Q e) = QInit (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "full_subst_vars \<sigma> (QApply Q e) = QApply (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "full_subst_vars \<sigma> (Measure X Q e) = Measure (map (subst_vars_c \<sigma>) X) (map (subst_vars_q \<sigma>) Q) (subst_vars_e \<sigma> e)"
| "full_subst_vars \<sigma> (C1; C2) = full_subst_vars \<sigma> C1; full_subst_vars \<sigma> C2"
| "full_subst_vars \<sigma> (IfTE e C1 C2) = IfTE (subst_vars_e \<sigma> e) (full_subst_vars \<sigma> C1) (full_subst_vars \<sigma> C2)"
| "full_subst_vars \<sigma> (While e C) = While (subst_vars_e \<sigma> e) (full_subst_vars \<sigma> C)"
| "full_subst_vars \<sigma> (Local v C) = Local (\<sigma> v) (full_subst_vars \<sigma> C)"

inductive no_conflict :: "(var\<Rightarrow>var) \<Rightarrow> context \<Rightarrow> bool" where
  nc_IfTE: "no_conflict \<sigma> c1 \<Longrightarrow> no_conflict \<sigma> c2 \<Longrightarrow> no_conflict \<sigma> (IfTE e c1 c2)"
| nc_Seq: "no_conflict \<sigma> c1 \<Longrightarrow> no_conflict \<sigma> c2 \<Longrightarrow> no_conflict \<sigma> (c1; c2)"
| nc_While: "no_conflict \<sigma> c \<Longrightarrow> no_conflict \<sigma> (While e c)"
| nc_Local: "no_conflict (\<sigma>(v:=v)) c \<Longrightarrow> v \<notin> \<sigma> ` (fv c \<inter> var_subst_dom \<sigma>)
             \<Longrightarrow> no_conflict \<sigma> (Local v c)"
| nc_Assign: "no_conflict \<sigma> (Assign _ _)"
| nc_Sample: "no_conflict \<sigma> (Sample _ _)"
| nc_QInit: "no_conflict \<sigma> (QInit _ _)"
| nc_QApply: "no_conflict \<sigma> (QApply _ _)"
| nc_Measure: "no_conflict \<sigma> (Measure _ _ _)"
| nc_Hole: "no_conflict \<sigma> (Hole _)"
| nc_Skip: "no_conflict \<sigma> (Skip)"


subsection \<open>Predicates\<close>

text \<open>A type for representing predicates (pre-/postconditions).\<close>
typedecl predicate

text \<open>This allows us to use \<open>A\<sqinter>B\<close> to write the intersection of predicates.\<close>
instance predicate :: inf..
text \<open>This allows us to use \<open>A\<le>B\<close> to write the inclusion (implication) of predicates.\<close>
instance predicate :: ord..
text \<open>This allows us to use \<open>\<top>\<close> to write the inclusion (implication) of predicates.\<close>
instance predicate :: top..

axiomatization fvp :: "predicate \<Rightarrow> var set"

text \<open>Represents an operator\<close>
typedecl operator
axiomatization identity :: operator

text \<open>The meaning of \<^term>\<open>Eq (U,V,W1,W2) V\<close> is $(U\<otimes>I)W1V_1 \equiv_q (V\<otimes>I)W2V_2$.\<close>
axiomatization Eq :: "(operator \<times> operator \<times> qvar list \<times> qvar list) \<Rightarrow> var set \<Rightarrow> predicate"

(* TODO remove *)
definition Eq0 where \<open>Eq0 = Eq (identity,identity,[],[])\<close>

text \<open>Applying variable substitutions on predicates. This constant is only define when the substitution
  is a bijection. (This is a simpler concept and stating all assumptions only for this case makes
  the trust-base smaller.) Full-fledged substitution is derived from this below.\<close>
axiomatization substp_bij :: "(var \<Rightarrow> var) \<Rightarrow> predicate \<Rightarrow> predicate"

definition "substp \<sigma> A = (let \<tau> = (SOME \<tau>. bij \<tau> \<and> valid_var_subst \<tau> \<and> (\<forall>x\<in>fvp A. \<tau> x = \<sigma> x)) in substp_bij \<tau> A)"

subsection \<open>Denotations and qRHL\<close>

axiomatization denot_eq :: "context \<Rightarrow> context \<Rightarrow> bool"
  where denot_eq_refl[simp]: "program C \<Longrightarrow> denot_eq C C"
    and denot_eq_sym: "program C \<Longrightarrow> program D \<Longrightarrow> denot_eq C D \<Longrightarrow> denot_eq D C"
    and denot_eq_cong_local: "program C \<Longrightarrow> program D \<Longrightarrow> denot_eq C D \<Longrightarrow> denot_eq (Local X C) (Local X D)"
    and denot_eq_trans[trans]: "program C \<Longrightarrow> program D \<Longrightarrow> program E \<Longrightarrow> denot_eq C D \<Longrightarrow> denot_eq D E \<Longrightarrow> denot_eq C E"

axiomatization qrhl :: "predicate \<Rightarrow> context \<Rightarrow> context \<Rightarrow> predicate \<Rightarrow> bool"

text \<open>More convenient derived notion of denotational equivalence that can also be applied to contexts.
  (Their holes are implicitly filled with skips.) In contrast, \<^const>\<open>denot_eq\<close> is only defined when
  its arguments are programs.\<close>
definition denot_eq' :: "context \<Rightarrow> context \<Rightarrow> bool" (infix "=d=" 50) where
  "C =d= D \<longleftrightarrow> denot_eq (substitute C (\<lambda>_. Skip)) (substitute D (\<lambda>_. Skip))"

text \<open>More convenient derive definition of qRHL judgments that can also be applied to contexts.
  (Their holes are implicitly filled with skips.) In contrast, \<^const>\<open>qrhl\<close> is only defined when
  its arguments are programs.\<close>
definition qRHL :: "predicate \<Rightarrow> context \<Rightarrow> context \<Rightarrow> predicate \<Rightarrow> bool" where
  "qRHL A C D B \<longleftrightarrow> qrhl A (substitute C (\<lambda>_. Skip)) (substitute D (\<lambda>_. Skip)) B"

end
