section \<open>Cylindric Kleene Lattices and Liberation Kleene Lattices\<close>

text \<open>Using this mathematical component requires downloading the Archive of Formal Proofs.\<close>

theory CKL
  imports Main  "~~/src/HOL/Library/Lattice_Syntax" 
          Kleene_Algebra.Kleene_Algebra 

begin

text \<open>Kleene algebras with a left zero are also known as weak Kleene algebras.\<close>

context kleene_algebra_zerol
begin

definition kplus :: "'a \<Rightarrow> 'a" ("_\<^sup>\<oplus>" [101] 100) where
  "x\<^sup>\<oplus> = x \<cdot> x\<^sup>\<star>"

lemma kplus_star: "x\<^sup>\<star> = 1 + x\<^sup>\<oplus>"
  by (simp add: kplus_def)

lemma kplus_star_opp: "x\<^sup>\<oplus> = x\<^sup>\<star> \<cdot> x"
  by (simp add: kplus_def local.star_slide_var)

lemma kplus_unfoldr [simp]: "x + x\<^sup>\<oplus> \<cdot> x = x\<^sup>\<oplus>"
  by (simp add: kplus_star_opp)

lemma kplus_unfoldl [simp]: "x + x \<cdot> x\<^sup>\<oplus> = x\<^sup>\<oplus>"
  using kplus_def kplus_star_opp kplus_unfoldr mult_assoc by auto

end

text \<open>We define weak l-monoids, weak residuated l-monoids, weak Kleene lattices and weak action lattices 
and prove some properties.\<close> 

class l_monoid_zerol = dioid_one_zerol + semilattice_inf +
  assumes absorp1 [simp]: "x + (x \<sqinter> y) = x"
  and absorp2 [simp]: "x \<sqinter> (x + y) = x"

begin

lemma meet_zeror [simp]: "x \<sqinter> 0 = 0"
  by (simp add: inf_absorb2)
  
end

class residuated_l_monoid_zerol = l_monoid_zerol +
  fixes fres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and bres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fres_adj: "(x \<cdot> y \<le> z) = (x \<le> fres z y)"
  and bres_adj: "(x \<cdot> y \<le> z) = (y \<le> bres x z)"

class kleene_lattice_zerol = l_monoid_zerol + kleene_algebra_zerol

begin

lemma star_meet: "(x \<sqinter> y)\<^sup>\<star> \<le> x\<^sup>\<star> \<sqinter> y\<^sup>\<star>"
  by (simp add: star_iso)

end

class action_lattice_zerol = kleene_lattice_zerol + residuated_l_monoid_zerol

class l_monoid = l_monoid_zerol + dioid_one_zero

class kleene_lattice = kleene_lattice_zerol + dioid_one_zero

begin

subclass l_monoid
  by unfold_locales

end

class action_lattice = action_lattice_zerol + dioid_one_zero

text \<open>Next we define weak cylindric l-monoids and prove some basic properties.\<close>

locale cylindric_l_monoid_zerol = 
  fixes cyl :: "'a \<Rightarrow> 'b::l_monoid_zerol \<Rightarrow> 'b"
  assumes cyl_ext: "x \<le> cyl i x"
  and cyl_sup_add: "cyl i (x + y) = (cyl i x) + (cyl i y)"
  and cyl_multl: "cyl i ((cyl i x) \<cdot> y) = (cyl i x) \<cdot> (cyl i y)"
  and cyl_multr: "cyl i (x \<cdot> cyl i y) = (cyl i x) \<cdot> (cyl i y)"
  and cyl_inf: "cyl i (x \<sqinter> (cyl i y)) = (cyl i x) \<sqinter> (cyl i y)"
  and cyl_zero [simp]: "cyl i 0 = 0"
  and cyl_comm: "cyl i (cyl j x) = cyl j (cyl i x)"
  and cyl_id_meet: "i \<noteq> j \<Longrightarrow> (cyl i 1) \<sqinter> (cyl j 1) = 1"
  and cyl_id_meet_pres: "cyl i ((cyl j 1) \<sqinter> (cyl k 1)) = (cyl i (cyl j 1)) \<sqinter> (cyl i (cyl k 1))"

begin 

lemma cyl_one_comm: "j \<noteq> k \<Longrightarrow> (cyl i (cyl j 1)) \<sqinter> (cyl i (cyl k 1)) = cyl i 1"
  by (metis cyl_id_meet cyl_id_meet_pres)

lemma cyl_zero_iff: "(cyl i x = 0) = (x = 0)"
  by (metis cyl_ext cyl_zero join.bot.extremum_unique)

lemma cyl_iso: "x \<le> y \<Longrightarrow> cyl i x \<le> cyl i y"
  by (metis cyl_sup_add less_eq_def)

lemma cyl_clos: "(x \<le> cyl i y) = (cyl i x \<le> cyl i y)"
  by (metis cyl_ext cyl_inf le_iff_inf order_trans)

lemma cyl_rel_prop_var1: "cyl i 1 \<cdot> x \<le> cyl i x"
  by (smt cyl_clos cyl_multl cyl_multr monoid.left_neutral mult.monoid_axioms order_refl)

lemma cyl_rel_prop_var2: "x \<cdot> cyl i 1 \<le> cyl i x"
  by (metis cyl_clos cyl_ext cyl_multl cyl_multr mult_oner)

lemma cyl_rel_prop: "cyl i 1 \<cdot> x \<cdot> cyl i 1 \<le> cyl i x"
  using cyl_clos cyl_rel_prop_var1 cyl_rel_prop_var2 order_trans by blast

lemma cyl_oplax: "cyl i (x \<cdot> y) \<le> cyl i x \<cdot> cyl i y"
  by (metis cyl_ext cyl_iso cyl_multr mult_isol)

lemma cyl_fix_prop: "cyl i x = x \<Longrightarrow> cyl i 1 \<cdot> x \<cdot> cyl i 1 = x"
  by (metis cyl_multl cyl_multr mult_onel mult_oner)

lemma cyl_fix_im: "(cyl i x = x) = (\<exists>y. cyl i y = x)"
  by (meson cyl_clos eq_iff)

lemma cyl_1_unl [simp]: "cyl i 1 \<cdot> cyl i x = cyl i x"
  by (metis cyl_fix_im cyl_multr mult_onel)

lemma cyl_1_unr [simp]: "cyl i x \<cdot> cyl i 1 = cyl i x"
  by (metis cyl_fix_im cyl_multl mult_oner)

lemma cyl_1_idem [simp]: "cyl i 1 \<cdot> cyl i 1 = cyl i 1"
  by simp

lemma cyl_conj: "(x \<sqinter> cyl i y = 0) = (y \<sqinter> cyl i x = 0)"
  by (metis cyl_inf cyl_zero_iff inf_commute)

lemma cyl_conj_var: "(cyl i x \<sqinter> cyl j y = 0) = (cyl j x \<sqinter> cyl i y = 0)"
  by (simp add: cyl_comm cyl_conj)

lemma cyl_1_zero [simp]: "cyl i 1 \<cdot> 0 = 0"
  by (metis cyl_zero cyl_1_unl)

lemma 
  assumes "\<forall>(x::'b) y. x \<le> 1 \<and> y \<le> 1 \<longrightarrow> x \<cdot> y = x \<sqinter> y"
  and "\<forall>(x::'b). x \<le> 1 \<longrightarrow> (\<exists>y. y \<le> 1 \<and> x + y = 1)"
  and "\<forall>(x::'b). x \<le> 1 \<longrightarrow> (\<exists>y. y \<le> 1 \<and> x \<sqinter> y = 0)"
  shows "x \<le> 1 \<Longrightarrow> cyl i 1 \<cdot> (cyl i x \<sqinter> 1) = cyl i x"
  (*nitpick*)
  oops

lemma cyl_inter_one: "x \<le> 1 \<Longrightarrow> cyl i (cyl i x \<sqinter> 1) = cyl i x"
  by (metis absorp2 cyl_inf cyl_sup_add inf_commute join.le_iff_sup)

lemma "x \<le> 1 \<Longrightarrow> cyl i x = cyl i 1 \<cdot> x \<cdot> cyl i 1 \<Longrightarrow> cyl i 1 \<cdot> (cyl i x \<sqinter> 1) = cyl i x"
  (*nitpick*)
  oops

lemma "x \<le> 1 \<Longrightarrow> cyl i (cyl j x \<sqinter> 1) = cyl j (cyl i x \<sqinter> 1)"
  (*nitpick*)
  oops

lemma "(cyl i 1) \<cdot> (cyl j 1) = (cyl j 1) \<cdot> (cyl i 1)"
  (*nitpick*)
  oops

lemma "(cyl i x = x) = (cyl i 1 \<cdot> x \<cdot> cyl i 1 = x)"
  (*nitpick*)
  oops

lemma "(\<forall> i x. cyl i x = cyl i 1 \<cdot> x \<cdot> cyl i 1) \<Longrightarrow> cyl i 1 \<cdot> cyl j 1 = cyl j 1 \<cdot> cyl i 1"
  (*nitpick*)
  oops

end

locale cylindric_l_monoid = cylindric_l_monoid_zerol cyl for cyl +
  constrains cyl :: "'a \<Rightarrow> 'b::l_monoid \<Rightarrow> 'b"

text \<open>Next we define weak cylindric Kleene lattices and prove some properties.\<close> 

locale cylindric_kleene_lattice_zerol = cylindric_l_monoid_zerol +
  assumes cyl_kplus: "cyl i (x\<^sup>\<oplus>) \<le> (cyl i x::'b::{l_monoid_zerol,kleene_algebra_zerol})\<^sup>\<oplus>"

begin

lemma cyl_star: "cyl i x\<^sup>\<star> \<le> cyl i 1 \<cdot> (cyl i x)\<^sup>\<star>"
  by (metis cyl_ext mult_isor mult_onel)

lemma cyl_cyl_kplus [simp]: "cyl i ((cyl i x)\<^sup>\<oplus>) = (cyl i x)\<^sup>\<oplus>"
  by (metis cyl_ext cyl_fix_im cyl_kplus order_class.order.antisym)

lemma cyl_kplus_onel [simp]: "cyl i 1 \<cdot> (cyl i x)\<^sup>\<oplus> = (cyl i x)\<^sup>\<oplus>"
  by (metis cyl_cyl_kplus cyl_1_unl)

lemma cyl_kplus_one_shift [simp]: "cyl i 1 \<cdot> (cyl i x)\<^sup>\<oplus> = (cyl i x)\<^sup>\<oplus> \<cdot> 1"
  by simp

lemma cyl_kplus_id [simp]: "(cyl i 1)\<^sup>\<oplus> = (cyl i 1)"
  by (simp add: kplus_def star_inductr_var_eq2)

lemma cyl_star_one: "cyl i ((cyl i x)\<^sup>\<star>) = cyl i 1 \<cdot> (cyl i x)\<^sup>\<star>"
  by (simp add: cyl_sup_add kplus_star semiring_class.distrib_left)

lemma cyl_star_one_shift: "cyl i 1 \<cdot> (cyl i x)\<^sup>\<star> = (cyl i x)\<^sup>\<star> \<cdot> cyl i 1"
  by (simp add: star_sim3)

lemma cyl_1_prop: "(cyl i 1)\<^sup>\<star> \<le> cyl i 1"
  by (simp add: local.cyl_ext star_inductl_one)

lemma cyl_star_id [simp]: "(cyl i 1)\<^sup>\<star> = cyl i 1"
  by (simp add: cyl_1_prop order_class.order.antisym)

lemma "(cyl i 1 \<cdot> x \<cdot> cyl i 1) \<sqinter> (cyl i 1 \<cdot> y \<cdot> cyl i 1) = cyl i 1 \<cdot> (x \<sqinter> (cyl i 1 \<cdot> y \<cdot> cyl i 1)) \<cdot> cyl i 1"
  (*nitpick*)
  oops

lemma  "(\<forall>x. cyl i x = cyl i 1 \<cdot> x \<cdot> cyl i 1) \<Longrightarrow> (\<forall>x. x \<cdot> 0 = 0) \<Longrightarrow> (cyl i 1 \<cdot> x) \<sqinter> (cyl i 1 \<cdot> y) = cyl i 1 \<cdot> (x \<sqinter> (cyl i 1 \<cdot> y))"
  (*nitpick*)
  oops

lemma  "(\<forall>x. cyl i x = cyl i 1 \<cdot> x \<cdot> cyl i 1) \<Longrightarrow> (\<forall>x. x \<cdot> 0 = 0) \<Longrightarrow> (x \<cdot> cyl i 1) \<sqinter> (y \<cdot> cyl i 1) = (x \<sqinter> (y \<cdot> cyl i 1)) \<cdot> cyl i 1"
  (*nitpick*)
  oops

lemma "cyl i 1 \<cdot> x\<^sup>\<oplus> \<cdot> cyl i 1 \<le> (cyl i 1 \<cdot> x)\<^sup>\<oplus> \<cdot> cyl i 1"
  (*nitpick*)
  oops

lemma "x \<le> 1 \<Longrightarrow> \<not>(\<exists>y. x = cyl i y)"
  (*nitpick*)
  oops

lemma "x < 1 \<Longrightarrow> cyl i x = x"
  (*nitpick*)
  oops

end

locale cylindric_kleene_lattice = cylindric_kleene_lattice_zerol cyl for cyl +
  constrains cyl :: "'a \<Rightarrow> 'b::kleene_lattice \<Rightarrow> 'b"

text \<open>We formalise a dual inner cylindrification in cylindric Kleene lattices.\<close>

locale dual_cylindric_kleene_lattice = 
  fixes cy :: "'a \<Rightarrow> 'b::kleene_lattice_zerol \<Rightarrow> 'b"
  and dcy :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes cy_adj: "(cy i x \<le> y) = (x \<le> dcy i y)"
  assumes cy_seq1: "cy i (x \<cdot> cy i y) = cy i x \<cdot> cy i y"
  and zy_seq2: "cy i (cy i x \<cdot> y) = cy i x \<cdot> cy i y"
  and dzy_le_zy: "dcy i x \<le> cy i x"
  and zy_meet: "cy i (x \<sqinter> cy i y) = cy i x \<sqinter> cy i y"
  and cy_dcy_semicomm: "cy i (dcy j x) \<le> dcy j (cy i x)"
  and dcy_one: "dcy i 1 = 0"
  and cy_kplus : "cy i (x\<^sup>\<oplus>) \<le> (cy i x)\<^sup>\<oplus>"
  and l6: "i \<noteq> j \<Longrightarrow> (cy i 1) \<sqinter> (cy j 1) = 1"
  and cyl_id_meet_pres: "cy i ((cy j 1) \<sqinter> (cy k 1)) = (cy i (cy j 1)) \<sqinter> (cy i (cy k 1))"

begin

lemma "dcy i (x + dcy i y) = dcy i x + dcy i y"
  (*nitpick*)
  oops

lemma cy_idem [simp]: "cy i (cy i x) = cy i x"
  by (smt cy_adj dzy_le_zy inf.absorb_iff1 inf.idem join.sup.orderE less_eq_def zy_meet)

lemma dcy_idem [simp]: "dcy i (dcy i x) = dcy i x"
  by (metis cy_adj cy_idem order_class.order.antisym order_refl)

lemma dcy_cy [simp]: "dcy i (cy i x) = cy i x"
  by (metis cy_adj cy_idem dzy_le_zy order_class.order.antisym order_refl)

lemma dcy_dzy [simp]: "cy i (dcy i x) = dcy i x"
  by (metis cy_adj dcy_cy order_class.order.antisym order_refl)

lemma cy_comm: "cy i (cy j x) = cy j (cy i x)"
  by (meson cy_adj cy_dcy_semicomm eq_iff order.trans)

lemma dcy_comm: "dcy i (dcy j x) = dcy j (dcy i x)"
  by (smt cy_adj cy_comm dcy_dzy eq_iff)

lemma cy_dcy_index_comm: "(cy i x \<le> dcy j y) = (cy j x \<le> dcy i y)"
  by (simp add: cy_adj dcy_comm)

lemma cy_iso: "x \<le> y \<Longrightarrow> cy i x \<le> cy i y"
  by (metis cy_adj inf.orderE le_infI2 order_refl)

lemma dcy_iso: "x \<le> y \<Longrightarrow> dcy i x \<le> dcy i y"
  by (meson cy_adj dual_order.trans order_refl)

lemma cy_sup_pres: "cy i (x + y) = cy i x + cy i y"
  by (meson cy_adj cy_iso join.le_sup_iff join.sup.cobounded1 join.sup.cobounded2 order_class.order.antisym)

lemma dcy_inf_pres: "dcy i (x \<sqinter> y) = dcy i x \<sqinter> dcy i y"
  by (meson cy_adj dcy_iso inf.cobounded1 inf.cobounded2 le_inf_iff order_class.order.antisym)

lemma cy_canc1: "cy i (dcy i x) \<le> x"
  using cy_adj by blast

lemma cy_canc3: "x \<le> dcy i (cy i x)"
  using cy_adj by blast

lemma cy_zero [simp]: "cy i 0 = 0"
  by (metis dcy_dzy dcy_one)
 
lemma cy_infl: "x \<le> cy i x"
  using cy_canc3 by auto

lemma dcy_infl: "dcy i x \<le> x"
  using cy_canc1 by auto

lemma cy_meet: "cy i (x \<cdot> dcy i y) = cy i x \<cdot> dcy i y"
  by (metis cy_seq1 dcy_dzy)

lemma cy_dcy_meet: "cy i (dcy i x \<cdot> y) = dcy i x \<cdot> cy i y"
  by (metis dcy_dzy zy_seq2)

lemma dcy_seq1: "dcy i x \<cdot> dcy i y \<le> dcy i (x \<cdot> dcy i y)"
  by (metis cy_adj cy_meet dcy_dzy dcy_infl mult_isor)

lemma dcy_seq2: "dcy i x \<cdot> dcy i y \<le> dcy i (dcy i x \<cdot> y)"
  by (metis cy_adj cy_dcy_meet dcy_dzy dcy_infl mult_isol)


lemma "dcy i x \<cdot> dcy i y = dcy i (x \<cdot> dcy i y)"
  (*nitpick*)
  oops

lemma "dcy i x \<cdot> dcy i y = dcy i (dcy i x \<cdot> y)"
  (*nitpick*) 
  oops

lemma dcy_meet_prop: "dcy i x \<cdot> dcy i y \<le> dcy i (x \<cdot> y)"
  by (metis cy_adj cy_dcy_meet dcy_dzy dcy_infl mult_isol_var)

lemma dcy_fix: "(dcy i x = x) = (\<exists>y. dcy i y = x)"
  by auto

lemma dcy_star: "(dcy i x)\<^sup>\<oplus> \<le> dcy i (x\<^sup>\<oplus>)"
  by (metis (no_types, lifting) cy_adj cy_canc3 cy_kplus dcy_dzy kplus_def mult_isol_var order_class.order.antisym star_iso)

lemma dcy_star_prop [simp]: "dcy i ((dcy i x)\<^sup>\<oplus>) = (dcy i x)\<^sup>\<oplus>"
  by (metis dcy_idem dcy_infl dcy_star eq_iff)

end

text \<open>Next we turn to weak liberation Kleene lattices.\<close>

locale liberation_l_monoid_zerol = 
  fixes lib :: "'a \<Rightarrow> 'b::l_monoid_zerol"
  assumes l1 [simp]: "lib i \<cdot> 0 = 0"
  and l2: "1 \<le> lib i"
  and l3: "lib i \<cdot> (x \<sqinter> ((lib i) \<cdot> y)) = ((lib i) \<cdot> x) \<sqinter> ((lib i) \<cdot> y)"
  and l4: "(x \<sqinter> (y \<cdot> lib i)) \<cdot> lib i = (x \<cdot> lib i) \<sqinter> (y \<cdot> lib i)"
  and l5: "(lib i) \<cdot> (lib j) = (lib j) \<cdot> (lib i)"
  and l6: "i \<noteq> j \<Longrightarrow> (lib i) \<sqinter> (lib j) = 1"
  and l7: "lib i \<cdot> (lib j \<sqinter> lib k) = (lib i \<cdot> lib j) \<sqinter> (lib i \<cdot> lib k)"
  and l8: "(lib i \<sqinter> lib j) \<cdot> lib k = (lib i \<cdot> lib k) \<sqinter> (lib j \<cdot> lib k)"

begin

lemma "i \<noteq> j \<Longrightarrow> i \<noteq> k \<Longrightarrow> j \<noteq> k \<Longrightarrow> (lib i \<cdot> lib j) \<sqinter> lib k = 1"
  (*nitpick*)
  oops

lemma "i \<noteq> j \<Longrightarrow> i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> j \<noteq> k \<Longrightarrow> j \<noteq> l \<Longrightarrow> k \<noteq> l \<Longrightarrow> (lib i \<cdot> lib j) \<sqinter> (lib k \<cdot> lib l) = 1"
  (*nitpick*)
  oops

lemma lib_annir [simp]: "lib i \<cdot> 0 \<cdot> lib i = 0"
  by simp

lemma lib_idem [simp]: "lib i \<cdot> lib i = lib i"
  by (metis inf.absorb2 l2 l3 mult_onel mult_oner order_refl phl_cons1)

lemma lib_double_add: "lib i \<cdot> (x + y) \<cdot> lib i = (lib i \<cdot> x \<cdot> lib i) + (lib i \<cdot> y \<cdot> lib i)"
  by (simp add: semiring_class.distrib_left)

lemma lib_seq1: "lib i \<cdot> x \<cdot> lib i \<cdot> y \<cdot> lib i \<cdot> lib i = lib i \<cdot> x \<cdot> lib i \<cdot> lib i \<cdot> y \<cdot> lib i"
  by (simp add: semigroup_mult_class.mult.assoc)

lemma lib_seq2: "lib i \<cdot> lib i \<cdot> x \<cdot> lib i \<cdot> y \<cdot> lib i = lib i \<cdot> x \<cdot> lib i \<cdot> lib i \<cdot> y \<cdot> lib i"
  by (simp add: semigroup_mult_class.mult.assoc)

lemma  lib_meet: "lib i \<cdot> (x \<sqinter> (lib i \<cdot> y \<cdot> lib i)) \<cdot> lib i = (lib i \<cdot> x \<cdot> lib i) \<sqinter> (lib i \<cdot> y \<cdot> lib i)"
  by (metis l3 l4 mult.assoc)

end

locale liberation_l_monoid = liberation_l_monoid_zerol lib for lib +
  constrains lib :: "'a \<Rightarrow> 'b::l_monoid"

locale liberation_kleene_lattice_zerol = liberation_l_monoid_zerol lib for lib +
  constrains lib :: "'a \<Rightarrow> 'b::kleene_lattice_zerol"

begin

lemma lib_kplus_prop1 [simp]: "(lib i \<cdot> x \<cdot> lib i)\<^sup>\<oplus> = (lib i \<cdot> x)\<^sup>\<oplus> \<cdot> lib i"
  by (simp add: conway.dagger_slide kplus_def mult.assoc)

lemma lib_star_prop: "lib i \<cdot> x\<^sup>\<oplus> \<cdot> lib i \<le> (lib i \<cdot> x)\<^sup>\<oplus> \<cdot> lib i"
proof -
  have "1 \<le> lib i"
    by (simp add: l2)
  then have "(x + x)\<^sup>\<star> \<cdot> (lib i \<cdot> (x \<cdot> x\<^sup>\<star>) + lib i \<cdot> (x \<cdot> x\<^sup>\<star>))\<^sup>\<star> = (lib i \<cdot> x)\<^sup>\<star>"
    by (metis (no_types) distrib_right join.sup_idem less_eq_def mult.assoc mult.left_neutral star_denest_var)
  then have "lib i \<cdot> x \<cdot> (lib i \<cdot> x)\<^sup>\<star> = (lib i \<cdot> (x \<cdot> x\<^sup>\<star>))\<^sup>\<oplus>"
    by (simp add: kplus_def mult.assoc)
  then show ?thesis
    by (metis (no_types) absorp2 inf.absorb_iff2 inf.commute kplus_def kplus_unfoldl mult_isor)
qed

lemma lib_kplus_prop2: "(lib i \<cdot> x)\<^sup>\<oplus> \<cdot> lib i = lib i \<cdot> (x \<cdot> lib i)\<^sup>\<oplus>"
  by (simp add: kplus_def mult.assoc star_slide)

lemma lib_cyll: "lib i \<cdot> x\<^sup>\<oplus> \<le> (lib i \<cdot> x)\<^sup>\<oplus>"
  by (metis (no_types, hide_lams) kplus_def l2 mult.assoc mult_isol mult_isor mult_onel star_iso)

lemma lib_cylr: "x\<^sup>\<oplus> \<cdot> lib i \<le> (x \<cdot> lib i)\<^sup>\<oplus>"
  by (smt conway.dagger_subdist join.sup_aci(1) kplus_def kplus_star_opp l2 lib_idem mult.assoc mult_double_iso star_denest_var sup_id_star1 tc_eq)

lemma [simp]: "lib i \<cdot> (lib i \<cdot> x)\<^sup>\<oplus> = (lib i \<cdot> x)\<^sup>\<oplus>"
  by (metis (no_types, lifting) kplus_def lib_idem mult.assoc)

lemma "lib i \<cdot> ((lib j) \<sqinter> (lib k)) = (lib i \<cdot> lib j) \<sqinter> (lib i \<cdot> lib k)"
  (*nitpick*)
  oops

lemma "lib i \<cdot> lib j = lib i + lib j"
  (*nitpick*)
  oops

end

locale liberation_kleene_lattice = liberation_kleene_lattice_zerol lib for lib +
  constrains lib :: "'a \<Rightarrow> 'b::kleene_lattice"

text \<open>Finally we formalise liberation action lattices. Ultimately this locale should be intergrated
whith the residuated lattice components in the AFP.\<close>

locale liberation_action_lattice_zerol = 
  fixes li :: "'a \<Rightarrow> 'b::action_lattice_zerol"
  assumes li1 [simp]: "li i \<cdot> 0 = 0"
  and li2: "1 \<le> li i"
  and li3: "li i \<cdot> (x \<sqinter> ((li i) \<cdot> y)) = ((li i) \<cdot> x) \<sqinter> ((li i) \<cdot> y)"
  and li4: "(x \<sqinter> (y \<cdot> li i)) \<cdot> li i = (x \<cdot> li i) \<sqinter> (y \<cdot> li i)"
  and li5: "(li i) \<cdot> (li j) = (li j) \<cdot> (li i)"
  and li6: "i \<noteq> j \<Longrightarrow> (li i) \<sqinter> (li j) = 1"
  and li7: "li i \<cdot> (li j \<sqinter> li k) = (li i \<cdot> li j) \<sqinter> (li i \<cdot> li k)"
  and li8: "(li i \<sqinter> li j) \<cdot> li k = (li i \<cdot> li k) \<sqinter> (li j \<cdot> li k)"
  and li9: "bres (li i) 1 = 0"
  and i10: "fres 1 (li i) = 0"

begin

abbreviation "cyl i x \<equiv> li i \<cdot> x \<cdot> li i"

abbreviation "dcyl i x \<equiv> bres (li i) (fres x (li i))"

lemma bres_fres_comm: "(bres x (fres y z)) = (fres (bres x y) z)"
  apply (rule antisym)
  by (metis (no_types, lifting) bres_adj dual_order.refl fres_adj mult.assoc)+

lemma li_bres_adj: "(li i \<cdot> x \<le> y) = (x \<le> bres (li i) y)"
  by (simp add: bres_adj)

lemma li_fres_asj: "(x \<cdot> li i \<le> y) = (x \<le> fres y (li i))"
  by (simp add: fres_adj)

lemma bres_prop: "bres (li i) x \<le> li i \<cdot> x"
  by (metis (no_types, hide_lams) bres_adj dual_order.trans li2 mult_isor mult_onel order_refl)

lemma fres_prop: "fres x (li i) \<le> x \<cdot> li i"
  by (metis (no_types, hide_lams) dual_order.trans fres_adj li2 mult_isol mult_oner order_refl)

lemma li_bres_swap: "(x \<le> bres (li i) y) \<Longrightarrow> (bres (li i) x \<le> y)"
  by (meson bres_adj bres_prop order.trans)
 
lemma li_fres_swap: "(x \<le> fres y (li i)) \<Longrightarrow> (fres x (li i) \<le> y)"
  by (meson dual_order.trans fres_adj fres_prop)

lemma li_bres_canc1: "(li i) \<cdot> (bres (li i) x) \<le> x"
  by (simp add: bres_adj)

lemma li_bres_canc2: "x \<le> bres (li i) ((li i) \<cdot> x)"
  using bres_adj by auto

lemma li_fres_canc1: "(fres x (li i)) \<cdot> li i \<le> x"
  by (simp add: fres_adj)

lemma li_fres_canc2: "x \<le> (fres (x \<cdot> (li i)) (li i))"
  using fres_adj by blast

lemma li_bres_prop [simp]: "(li i) \<cdot> (bres (li i) x) = bres (li i) x"
  by (smt antisym bres_prop inf.absorb_iff2 li2 li3 li_bres_adj li_bres_canc1 li_bres_canc2 mult.assoc mult_onel mult_oner order.trans phl_cons2 phl_skip)
 
lemma bres_li_prop [simp]: "bres (li i) (li i \<cdot> x) = li i \<cdot> x"
  by (metis antisym li_bres_canc1 li_bres_canc2 li_bres_prop mult_isol)

lemma li_fres_prop [simp]: "(fres x (li i)) \<cdot> li i = fres x (li i)"
  by (smt fres_adj fres_prop inf.absorb_iff2 inf_commute li4 li_fres_canc1)
 
lemma fres_li_prop [simp]: "fres (x \<cdot> li i) (li i) = x \<cdot> li i"
  by (metis antisym li_fres_canc1 li_fres_canc2 li_fres_prop mult_isor)

lemma bres_bres_li [simp]: "bres (li i) (bres (li i) x) = bres (li i) x"
  by (metis bres_li_prop li_bres_prop)

lemma fres_fres_li [simp]: "fres (fres x (li i)) (li i) = fres x (li i)"
  by (metis fres_li_prop li_fres_prop)

lemma bres_li_defl: "bres (li i) x \<le> x"
  using li_bres_canc1 li_bres_prop by auto

lemma fres_li_defl: "fres x (li i) \<le> x"
  using li_fres_canc1 li_fres_prop by auto

lemma bres_li_zero [simp]: "bres (li i) 0 = 0"
  by (metis bres_li_prop li1)
  
lemma fres_li_zero [simp]: "fres 0 (li i) = 0"
  by (simp add: fres_li_defl join.bot.extremum_uniqueI)

lemma bres_iso: "x \<le> y \<Longrightarrow> bres z x \<le> bres z y"
  by (meson bres_adj dual_order.refl order.trans)

lemma fres_iso: "x \<le> y \<Longrightarrow> fres x z \<le> fres y z"
  using dual_order.trans fres_adj by blast

lemma cyl_idem [simp]: "cyl i (cyl i x) = cyl i x"
  by (metis bres_li_prop fres_li_prop li_bres_prop li_fres_prop mult.assoc)

lemma dcyl_idem: "dcyl i (dcyl i x) = dcyl i x"
  by (simp add: bres_fres_comm)

lemma cyl_dcyl [simp]: "cyl i (dcyl i x) = dcyl i x"
  by (metis bres_fres_comm li_bres_prop li_fres_prop)

lemma dyl_cyl [simp]: "dcyl i (cyl i x) = cyl i x"
  by (metis bres_li_prop fres_li_prop mult.assoc)

lemma cyl_dcyl_adj: "(cyl i x \<le> y) = (x \<le> dcyl i y)"
  using bres_adj fres_adj by blast

lemma dcyl_defl: "dcyl i x \<le> x"
  using bres_li_defl fres_li_defl order.trans by blast

lemma dcyl_le_cyl: "dcyl i x \<le> cyl i x"
  by (metis cyl_dcyl_adj fres_li_defl fres_li_prop li_bres_swap mult_double_iso)

lemma dcyl_ij_comm: "dcyl i (dcyl j x) = dcyl j (dcyl i x)"
  apply (rule antisym)
  by (smt li5 liberation_action_lattice_zerol.cyl_dcyl liberation_action_lattice_zerol.cyl_dcyl_adj liberation_action_lattice_zerol.dcyl_defl liberation_action_lattice_zerol_axioms mult.assoc)+

lemma cyl_dcyl_swap: "cyl i (dcyl j x) \<le> dcyl j (cyl i x)"
  by (metis bres_adj bres_iso cyl_dcyl_adj dcyl_ij_comm fres_iso li_fres_canc2)

lemma dcyl_zero [simp]: "dcyl i 1 = 0"
  by (simp add:  i10)

lemma dcyl_add: "dcyl i (x + dcyl i y) = dcyl i x + dcyl i y"
  (*nitpick*)
  oops

lemma dcyl_kplus: "(dcyl i x)\<^sup>\<oplus> \<le> dcyl i (x\<^sup>\<oplus>)"
  by (smt cyl_dcyl cyl_dcyl_adj dcyl_defl kplus_def kplus_star_opp li_bres_prop mult.assoc mult_isol_var star_iso)

lemma dcyl_kplus_prop [simp]: "dcyl i ((dcyl i x)\<^sup>\<oplus>) = (dcyl i x)\<^sup>\<oplus>"
  by (metis antisym dcyl_defl dcyl_idem dcyl_kplus)

end

end