section \<open>Cylindric Conway Lattices\<close>

text \<open>Using this file requires downloading the Archive of Formal Proofs.\<close>

theory Cylindric_Conway_Lattice
  imports Main  "~~/src/HOL/Library/Lattice_Syntax" 
          Kleene_Algebra.Kleene_Algebra 

begin

text \<open>Conway algebras are a common basis for Kleene algebras and demonic refinement algebras. We use weak variants 
in which a left distributivity law is absent most of the time, and sometimes replaced by an isotonicity law. This makes 
the approach applicable for instance for probabilistic variants and algebras of general or order-preserving predicate 
transformers.\<close>

text \<open>In near-semirings, there is no left distributivity law.\<close>

context near_conway_base
begin

definition kplus :: "'a \<Rightarrow> 'a" ("_\<^sup>\<oplus>" [101] 100) where
  "x\<^sup>\<oplus> = x \<cdot> x\<^sup>\<dagger>"

lemma kplus_dagger: "x\<^sup>\<dagger> = 1 + x\<^sup>\<oplus>"
  by (simp add: kplus_def)

end

text \<open>In presemirings, composition preserves the order in its second argument.\<close>

context pre_conway
begin

lemma kplus_opp:  "x\<^sup>\<oplus> = x\<^sup>\<dagger> \<cdot> x"
  by (metis dagger_denest dagger_prod_unfold dagger_slide dagger_unfoldr_eq join.sup.idem kplus_dagger kplus_def)

lemma kplus_unfoldr [simp]: "x + x\<^sup>\<oplus> \<cdot> x = x\<^sup>\<oplus>"
  by (metis kplus_def dagger_slide dagger_unfoldl_distr mult_onel mult_oner)

lemma kplus_unfoldl [simp]: "x + x \<cdot> x\<^sup>\<oplus> = x\<^sup>\<oplus>"
  by (metis kplus_def kplus_unfoldr dagger_unfoldl_distr mult_assoc)

end

class near_l_monoid = near_dioid_one + semilattice_inf +
  assumes absorp1 [simp]: "x + (x \<sqinter> y) = x"
  and absorp2 [simp]: "x \<sqinter> (x + y) = x"

class near_l_monoid_zerol = near_l_monoid + near_dioid_one_zerol

begin

lemma meet_zeror [simp]: "x \<sqinter> 0 = 0"
  by (simp add: inf_absorb2)
  
end

text \<open>We consider a unary case of cylindrification where the axiom for different coordinates is absent. This is simpler
because we can use type classes instead of locales.\<close>

class cylindric_near_dioid_un_base = near_dioid_one +
  fixes cyl :: "'a \<Rightarrow> 'a"
  assumes cyl_ext: "x \<le> cyl x"
  and cyl_sup_add: "cyl (x + y) \<le> cyl x + cyl y"
  and cyl_multl: "cyl (cyl x \<cdot> y) = cyl x \<cdot> cyl y"
  and cyl_multr: "cyl (x \<cdot> cyl y) = cyl x \<cdot> cyl y"

text \<open>We deal with annihilators separately. Most properties do not depend on them.\<close>

class cylindric_near_dioid_zerol_un_base = cylindric_near_dioid_un_base + near_dioid_one_zerol +
  assumes cyl_zero [simp]: "cyl 0 = 0"

begin

lemma c1_iff: "(cyl x = 0) = (x = 0)"
  using cyl_ext cyl_zero join.le_bot by blast

end

text \<open>For dioids we need a slightly different set of cylindrification axioms than for l-monoids.\<close>

class cylindric_near_dioid_un = cylindric_near_dioid_un_base +
  assumes cyl_sub_add: "cyl x \<le> cyl (x + y)"
  and cyl_idem [simp]: "cyl (cyl x) = cyl x"

begin

lemma c3_iff:  "cyl (x + y) = cyl x + cyl y"
  by (smt add_commute add_iso cyl_sup_add cyl_sub_add join.sup.orderE)

lemma cyl_iso: "x \<le> y \<Longrightarrow> cyl x \<le> cyl y"
  by (metis c3_iff less_eq_def)

lemma cyl_clos: "(x \<le> cyl y) = (cyl x \<le> cyl y)"
  by (metis cyl_iso cyl_ext cyl_idem dual_order.trans)

lemma cyl1_prop1: "cyl 1 \<cdot> x \<cdot> cyl 1 \<le> cyl x"
  by (metis cyl_ext cyl_multl cyl_multr cyl_idem mult_1_left mult_oner)

lemma cyl1_prop2: "cyl 1 \<cdot> x \<le> cyl x"
  by (metis cyl_ext cyl_multl cyl_multr cyl_idem mult_onel)

lemma cyl1_prop3: "x \<cdot> cyl 1 \<le> cyl x"
  by (metis cyl_ext cyl_multl cyl_multr cyl_idem mult_1_right)

lemma cyl_oplax: "cyl (x \<cdot> y) \<le> cyl x \<cdot> cyl y"
  by (metis cyl_iso cyl_ext cyl_multl mult_isor)

lemma "cyl x = x \<Longrightarrow> cyl 1 \<cdot> x \<cdot> cyl 1 = x"
  by (metis cyl_multl cyl_multr mult_1_left mult_oner)

lemma cyl_fix_im: "(cyl x = x) = (\<exists>y. cyl y = x)"
  using cyl_idem by auto

lemma cyl_1_unl [simp]: "cyl 1 \<cdot> cyl x = cyl x"
  by (metis cyl_multr cyl_idem mult_1_left)

lemma cyl_1_unr [simp]: "cyl x \<cdot> cyl 1 = cyl x"
  by (metis cyl_multl cyl_idem mult_1_right)

lemma cyl_1_idem [simp]: "cyl 1 \<cdot> cyl 1 = cyl 1"
  by simp

end

text \<open>Here are the axioms for l-monoids.\<close>

class cylindric_near_l_monoid_un = near_l_monoid + cylindric_near_dioid_un_base +
  assumes cyl_inf: "cyl (x \<sqinter> cyl y) = cyl x \<sqinter> cyl y"

begin

text \<open>Every cylindric near-l-monoid is a cylindric near dioid --- with one coordinate.\<close>

subclass cylindric_near_dioid_un
  apply unfold_locales
  apply (metis cyl_ext cyl_inf inf.order_iff join.sup.bounded_iff)
  by (metis cyl_ext cyl_inf inf.orderE inf_absorb2)

end

class cylindric_near_l_monoid_zerol_un = cylindric_near_l_monoid_un + cylindric_near_dioid_zerol_un_base 

begin

lemma cyl_conj: "(x \<sqinter> cyl y = 0) = (y \<sqinter> cyl x = 0)"
  by (metis cyl_ext cyl_zero cyl_inf inf.commute join.le_bot)

lemma "cyl 1 \<cdot> x \<cdot> cyl 1 = cyl x"
  (*nitpick*)
  oops

text \<open>The following property holds in the relational model, but not in general.\<close>

lemma "(cyl x = x) = (cyl 1 \<cdot> x \<cdot> cyl 1 = x)"
  (*nitpick*)
  oops

end

text \<open>Next we consider iteration ... in fact the plus, we could do without a monoidal unit. We start with
near-dioids without a zero.\<close> 

class cylindric_near_conway_un = cylindric_near_dioid_un + near_conway_base +
  assumes cyl_kplus: "cyl (x\<^sup>\<oplus>) \<le> (cyl x)\<^sup>\<oplus>"

begin

lemma cyl_dagger: "cyl x\<^sup>\<dagger> \<le> cyl 1 \<cdot> (cyl x)\<^sup>\<dagger>"
  by (metis cyl_ext mult_isor mult_onel)

lemma cyl_cyl_kplus [simp]: "cyl ((cyl x)\<^sup>\<oplus>) = (cyl x)\<^sup>\<oplus>"
  by (metis antisym cyl_ext cyl_kplus cyl_idem)

lemma cyl_kplus_onel [simp]: "cyl 1 \<cdot> (cyl x)\<^sup>\<oplus> = (cyl x)\<^sup>\<oplus>"
  by (metis cyl_cyl_kplus cyl_1_unl)

lemma cyl_kplus_one_shift [simp]: "cyl 1 \<cdot> (cyl x)\<^sup>\<oplus> = (cyl x)\<^sup>\<oplus> \<cdot> 1"
  by simp

lemma "(cyl 1)\<^sup>\<oplus> \<le> (cyl 1)"
  (*nitpick*)
  oops

end

text \<open>Some properties require order-preservation in the second argument of multiplication.\<close>

class cylindric_pre_conway_un = cylindric_near_conway_un + pre_conway_base

begin

lemma cyl_dagger_one: "cyl ((cyl x)\<^sup>\<dagger>) = cyl 1 \<cdot> (cyl x)\<^sup>\<dagger>"
  by (metis c3_iff cyl1_prop2 cyl_cyl_kplus cyl_kplus_onel dual_order.antisym kplus_dagger mult_1_right subdistl_var)

lemma cyl_star_one_shift: "cyl 1 \<cdot> (cyl x)\<^sup>\<dagger> = (cyl x)\<^sup>\<dagger> \<cdot> cyl 1"
  by (metis cyl_dagger_one c3_iff cyl_1_unr cyl_cyl_kplus dagger_unfoldl_distr kplus_dagger kplus_def)

end

text \<open>For Conway algebras based on near-l-monoids we have no special properties.\<close>

class near_conway_lattice = near_l_monoid + near_conway_base

begin

lemma dagger_meet: "(x \<sqinter> y)\<^sup>\<dagger> \<le> x\<^sup>\<dagger> \<sqinter> y\<^sup>\<dagger>"
  by (simp add: local.dagger_iso)
 
end

class cylindric_near_conway_lattice_un = cylindric_near_conway_un + near_conway_lattice

class near_conway_lattice_zerol = near_conway_lattice + near_conway_base_zerol

text \<open>Next, for the relational case, we present an alternative formalisation based on cylindrified units. 
First we show that the axioms, which follow below, can be derived in Conway algebras.\<close>

class cylindric_near_conway_lattice_zerol_un = cylindric_near_conway_lattice_un + cylindric_near_l_monoid_zerol_un   

begin

lemma cyl_1_zero: "cyl 1 \<cdot> 0 = 0"
  by (metis cyl_zero cyl_1_unl)

lemma "1 \<le> cyl 1"
  by (simp add: cyl_ext)

lemma "cyl 1 \<cdot> cyl 1 = cyl 1"
  by simp

lemma "(cyl 1 \<cdot> x \<cdot> cyl 1) \<sqinter> (cyl 1 \<cdot> y \<cdot> cyl 1) = cyl 1 \<cdot> (x \<sqinter> (cyl 1 \<cdot> y \<cdot> cyl 1)) \<cdot> cyl 1"
  (*nitpick*)
  oops

lemma "(\<forall>x. cyl x = cyl 1 \<cdot> x \<cdot> cyl 1) \<Longrightarrow> (cyl 1 \<cdot> x \<cdot> cyl 1) \<sqinter> (cyl 1 \<cdot> y \<cdot> cyl 1) = cyl 1 \<cdot> (x \<sqinter>  (cyl 1 \<cdot> y \<cdot> cyl 1)) \<cdot> cyl 1"
  by (metis cyl_inf)

lemma  "(\<forall>x. cyl x = cyl 1 \<cdot> x \<cdot> cyl 1) \<Longrightarrow> (\<forall>x. x \<cdot> 0 = 0) \<Longrightarrow> (cyl 1 \<cdot> x) \<sqinter> (cyl 1 \<cdot> y) = cyl 1 \<cdot> (x \<sqinter> (cyl 1 \<cdot> y))"
  (*nitpick*)
  oops

lemma  "(\<forall>x. cyl x = cyl 1 \<cdot> x \<cdot> cyl 1) \<Longrightarrow> (\<forall>x. x \<cdot> 0 = 0) \<Longrightarrow> (x \<cdot> cyl 1) \<sqinter> (y \<cdot> cyl 1) = (x \<sqinter> (y \<cdot> cyl 1)) \<cdot> cyl 1"
  (*nitpick*)
  oops

lemma "cyl 1 \<cdot> x\<^sup>\<oplus> \<cdot> cyl 1 \<le> (cyl 1 \<cdot> x)\<^sup>\<oplus> \<cdot> cyl 1"
  (*nitpick*)
  oops

lemma "(\<forall>x. cyl x = cyl 1 \<cdot> x \<cdot> cyl 1) \<Longrightarrow> cyl 1 \<cdot> x\<^sup>\<oplus> \<cdot> cyl 1 \<le> (cyl 1 \<cdot> x \<cdot> cyl 1)\<^sup>\<oplus>"
  by (metis cyl_kplus)

end

class cylindric_kleene_lattice_zerol_un = cylindric_near_conway_lattice_zerol_un + kleene_algebra_zerol

begin

definition "klplus x = x \<cdot> x\<^sup>\<star>"


lemma cyl_1_ast:"(cyl 1)\<^sup>\<star> \<le> cyl 1"
  by (simp add: local.cyl_ext local.star_inductl_one)

lemma cyl1_ast_eq [simp]: "(cyl 1)\<^sup>\<star> = cyl 1"
  by (simp add: local.boffa local.cyl_ext local.join.sup.absorb2)

lemma klplus_1: "klplus (cyl 1) \<le> cyl 1"  
  by (simp add: klplus_def local.star_inductr_var_eq2)

lemma klplus_1_eq [simp]: "klplus (cyl 1) = cyl 1"
  by (simp add: klplus_def local.star_inductr_var_eq2)

lemma "x \<le> 1 \<Longrightarrow> \<not>(\<exists>y. x = cyl y)"
  (*nitpick*)
  oops

lemma "x < 1 \<Longrightarrow> cyl x = x"
  (*nitpick*)
  oops

end

text \<open>Next we present the axiomatisation with cylindrified units that works for relations.\<close>

class cy_conway_zerol = conway_base_zerol + near_l_monoid +
  fixes cy :: "'a"
  assumes cy1 [simp]: "cy \<cdot> 0 = 0"
  assumes cy2: "1 \<le> cy"
  assumes cy3: "cy \<cdot> cy \<le> cy"
  assumes cy4: "(cy \<cdot> x \<cdot> cy) \<sqinter> (cy \<cdot> y \<cdot> cy) \<le> cy \<cdot> (x \<sqinter> (cy \<cdot> y \<cdot> cy)) \<cdot> cy"

begin

lemma kplus_prop: "cy \<cdot> x\<^sup>\<oplus> \<cdot> cy \<le> (cy \<cdot> x)\<^sup>\<oplus> \<cdot> cy"
  by (metis local.cy2 local.dagger_iso local.kplus_def local.mult_1_left local.mult_isol local.mult_isor mult_assoc)

lemma cy_annir [simp]: "cy \<cdot> 0 \<cdot> cy = 0"
  by simp

lemma cy_idem [simp]: "cy \<cdot> cy = cy"
  using cy2 cy3 eq_iff mult_isol_var by fastforce

lemma cy_kplus_prop1 [simp]: "(cy \<cdot> x \<cdot> cy)\<^sup>\<oplus> = (cy \<cdot> x)\<^sup>\<oplus> \<cdot> cy"
  by (metis cy_idem local.dagger_slide_eq local.kplus_def mult_assoc)

lemma cy_kplus_prop2: "(cy \<cdot> x)\<^sup>\<oplus> \<cdot> cy = cy \<cdot> (x \<cdot> cy)\<^sup>\<oplus>"
  by (simp add: dagger_slide_eq kplus_def mult_assoc)

lemma cy_add: "cy \<cdot> (x + y) \<cdot> cy = (cy \<cdot> x \<cdot> cy) + (cy \<cdot> y \<cdot> cy)"
  by (simp add: distrib_left)

lemma cy_seq1: "cy \<cdot> x \<cdot> cy \<cdot> y \<cdot> cy \<cdot> cy = cy \<cdot> x \<cdot> cy \<cdot> cy \<cdot> y \<cdot> cy"
  by (simp add: mult_assoc)

lemma cy_seq2: "cy \<cdot> cy \<cdot> x \<cdot> cy \<cdot> y \<cdot> cy = cy \<cdot> x \<cdot> cy \<cdot> cy \<cdot> y \<cdot> cy"
  by (simp add: mult_assoc)

lemma  cy_meet: "cy \<cdot> (x \<sqinter> (cy \<cdot> y \<cdot> cy)) \<cdot> cy \<le> (cy \<cdot> x \<cdot> cy) \<sqinter> (cy \<cdot> y \<cdot> cy)"
  by (metis cy_idem inf.boundedI inf.cobounded1 inf.cobounded2 mult_double_iso mult_assoc)

end

text \<open>A formalisation of liberation algebras with one cylindrified unit follows.\<close>

class cyy_conway_zerol = conway_base_zerol + near_l_monoid +
  assumes cyy1: "cyy \<cdot> 0 \<le> 0"
  assumes cyy2: "1 \<le> cyy"
  assumes cyy4l: "(cyy \<cdot> x) \<sqinter> (cyy \<cdot> y) = cyy \<cdot> (x \<sqinter> (cyy \<cdot> y))"
  assumes cyy4r: "(x \<cdot> cyy) \<sqinter> (y \<cdot> cyy) = (x \<sqinter> (y \<cdot> cyy)) \<cdot> cyy"

begin 

lemma cyy_trans: "cyy \<cdot> cyy \<le> cyy"
  by (metis local.cyy2 local.cyy4l local.inf.absorb_iff1 local.mult_oner)

lemma cyy_kplus: "cyy \<cdot> x\<^sup>\<oplus> \<le> (cyy \<cdot> x)\<^sup>\<oplus>"
  by (metis local.cyy2 local.dagger_iso local.kplus_def local.mult_1_left local.mult_isol local.mult_isor mult_assoc)

lemma cyy_kplus_var: "x\<^sup>\<oplus> \<cdot> cyy \<le> (x \<cdot> cyy)\<^sup>\<oplus>"
proof -
have f1: "\<forall>a. (a::'a)\<^sup>\<dagger> \<cdot> a = a\<^sup>\<oplus>"
by (metis local.dagger_slide_eq local.kplus_def local.mult_1_left mult_assoc)
  have "\<forall>a aa. (aa::'a)\<^sup>\<oplus> \<le> aa \<cdot> a \<or> \<not> aa\<^sup>\<dagger> \<le> a"
    using local.kplus_def local.mult_isol by force
then show ?thesis
  using f1 by (metis local.cyy2 local.dagger_iso local.dagger_slide_eq local.mult_1_left local.mult_isor mult_assoc)
qed
 
lemma cyy_meet: "(cyy \<cdot> x \<cdot> cyy) \<sqinter> (cyy \<cdot> y \<cdot> cyy) = cyy \<cdot> (x \<sqinter> (cyy \<cdot> y \<cdot> cyy)) \<cdot> cyy"
  by (metis local.cyy4l local.cyy4r mult_assoc)

lemma cyy_double_kplus: "cyy \<cdot> x\<^sup>\<oplus> \<cdot> cyy \<le> (cyy \<cdot> x)\<^sup>\<oplus> \<cdot> cyy"
  by (simp add: cyy_kplus local.mult_isor)

lemma cyy_right_kplus: "cyy \<cdot> (cyy \<cdot> x)\<^sup>\<oplus> = (cyy \<cdot> x)\<^sup>\<oplus>"
  by (metis local.absorp2 local.cyy4l local.dagger_ext local.dagger_slide_var1_eq local.dagger_unfoldl_distr local.inf.commute local.inf.orderE local.kplus_def local.mult_1_right mult_assoc)
 
lemma "1\<^sup>\<dagger> \<le> 1 \<Longrightarrow> cyy\<^sup>\<dagger> \<le> cyy"
  (*nitpick*)
  oops

end

text \<open>Finally we outline the first steps towards dual cylindrification.\<close>

class l_monoid_zerol = near_l_monoid_zerol + near_dioid_one_zerol

class dual_cylindric_l_monoid = l_monoid_zerol +
  fixes zy :: "'a \<Rightarrow> 'a"
  and dzy :: "'a \<Rightarrow> 'a"
  assumes zy_adj: "(zy x \<le> y) = (x \<le> dzy y)"
  assumes zy_seq1: "zy (x \<cdot> zy y) = zy x \<cdot> zy y"
  and zy_seq2: "zy (zy x \<cdot> y) = zy x \<cdot> zy y"
  and dzy_le_zy: "dzy x \<le> zy x"
  and zy_meet: "zy (x \<sqinter> zy y) = zy x \<sqinter> zy y"
  and dzy_join: "dzy (x + dzy y) = dzy x + dzy y"

begin

lemma dzy_zy: "dzy (zy x) = zy x"
  by (metis local.dzy_le_zy local.eq_refl local.inf.absorb_iff1 local.inf_absorb2 local.zy_adj local.zy_meet)

lemma zy_dzy: "zy (dzy x) = dzy x"
  by (metis dzy_zy local.eq_iff local.zy_adj)

lemma zy_iso: "x \<le> y \<Longrightarrow> zy x \<le> zy y"
  using local.order.trans local.zy_adj by blast

lemma dzy_iso: "x \<le> y \<Longrightarrow> dzy x \<le> dzy y"
  using local.order_trans local.zy_adj by blast

lemma zy_sup_pres: "zy (x + y) = zy x + zy y"
  apply (rule antisym)
  using local.zy_adj apply fastforce
  by (simp add: zy_iso)
  
lemma ccyl_inf_pres: "dzy (x \<sqinter> y) = dzy x \<sqinter> dzy y"
  apply (rule antisym)
  apply (simp add: dzy_iso)
  by (meson local.inf.boundedI local.inf.cobounded1 local.inf.cobounded2 local.zy_adj)

lemma cyl_canc1: "zy (dzy x) \<le> x"
  using local.zy_adj by auto

lemma cyl_canc3: "x \<le> dzy (zy x)"
  using local.zy_adj by blast

lemma cyl_zero: "zy 0 = 0"
  by (simp add: local.antisym local.zy_adj)

lemma cyl_infl: "x \<le> zy x"
  using cyl_canc3 local.dzy_zy by auto

lemma dzy_defl: "dzy x \<le> x"
  using cyl_canc1 local.zy_dzy by auto

lemma zy_dzy1: "zy (x \<cdot> dzy y) = zy x \<cdot> dzy y"
  by (metis local.zy_seq1 zy_dzy)

lemma dy_dzy2: "zy (dzy x \<cdot> y) = dzy x \<cdot> zy y"
  by (metis local.zy_seq2 zy_dzy)

end

end