section \<open>Kleene Lattice Modules and Cylindric Lattice Modules\<close>

text \<open>Using this mathematical component requires downloading the Archive of Formal Proofs.\<close>

theory CKL_Module
  imports CKL

begin

text \<open>This component shows that the semidirect product of a Kleene lattice and a 
lattice with a least element forms a weak Kleene lattice. It also shows that the semidirect product 
of a liberation Kleene lattice and a lattice with a least element forms a weak liberation Kleene lattice.
This is useful for establishing properties of relational fault models.\<close>

locale l_monoid_module =
  fixes act :: "'a::l_monoid \<Rightarrow> 'b::bounded_lattice_bot \<Rightarrow> 'b" ("\<alpha>") 
  assumes m1: "\<alpha> (x \<cdot> y) p = \<alpha> x (\<alpha> y p)"
  and m2: "\<alpha> (x + y) p = \<alpha> x p \<squnion> \<alpha> y p"
  and m3: "\<alpha> x (p \<squnion> q) = \<alpha> x p \<squnion> \<alpha> x q"
  and m4 [simp]: "\<alpha> 1 p = p"
  and m5 [simp]: "\<alpha> 0 p = \<bottom>"

begin

lemma act_zero [simp]: "\<alpha> x \<bottom> = \<bottom>"
  by (metis annir m1 m5)

end

declare[[show_types]]
declare[[show_sorts]]

locale kleene_lattice_module = l_monoid_module \<alpha> for \<alpha> +
  assumes m6: "p \<squnion> \<alpha> (x::'a::kleene_lattice) q \<le> q \<Longrightarrow> \<alpha> (x\<^sup>\<star>) p \<le> q"

locale cylindric_kleene_lattice_module = cylindric_kleene_lattice cyl + kleene_lattice_module \<alpha> for cyl \<alpha> +
  constrains cyl :: "'a \<Rightarrow> 'b::kleene_lattice \<Rightarrow> 'b"
  and \<alpha> :: "'b \<Rightarrow> 'c::bounded_lattice_bot \<Rightarrow> 'c"

locale liberation_kleene_lattice_module = liberation_kleene_lattice lib + kleene_lattice_module \<alpha> for lib \<alpha> +
  constrains lib :: "'a \<Rightarrow> 'b::kleene_lattice"
  and \<alpha> :: "'b \<Rightarrow> 'c::bounded_lattice_bot \<Rightarrow> 'c"

definition "plus_prod (x::'a::l_monoid \<times> 'b::bounded_lattice_bot) y = (fst x + fst y,snd x \<squnion> snd y)"

definition "meet_prod (x::'a::l_monoid \<times> 'b::bounded_lattice_bot) y = (fst x \<sqinter> fst y, snd x \<sqinter> snd y)"

definition "zero_prod = (0,\<bottom>)"

definition "one_prod = (1,\<bottom>)"

definition  "le_prod x y = (fst x \<le> fst y \<and> snd x \<le> snd y)"

context l_monoid_module
begin

lemma plus_prod_assoc: "plus_prod x (plus_prod y z) = plus_prod (plus_prod x y) z"
  unfolding plus_prod_def by (simp add: join.sup_assoc sup_assoc)

lemma plus_prod_comm: "plus_prod x y = plus_prod y x"
  unfolding plus_prod_def by (simp add: inf_sup_aci(5) join.sup.commute)

lemma plus_prod_idem [simp]: "plus_prod x x = x"
  unfolding plus_prod_def by simp

lemma meet_prod_assoc: "meet_prod x (meet_prod y z) = meet_prod (meet_prod x y) z"
  unfolding meet_prod_def by (simp add: inf.assoc)

lemma meet_prod_comm: "meet_prod x y = meet_prod y x"
  unfolding meet_prod_def by (simp add: inf_commute)

lemma meet_prod_idem [simp]: "meet_prod x x = x"
  by (simp add: meet_prod_def)

lemma plus_meet_prod_absorp1 [simp]: "plus_prod x (meet_prod x y) = x"
  unfolding plus_prod_def meet_prod_def by simp

lemma plus_meet_prod_absorp2 [simp]: "meet_prod x (plus_prod x y) = x"
  unfolding plus_prod_def meet_prod_def by simp

lemma zero_prod_least1 [simp]: "plus_prod x zero_prod = x"
  unfolding plus_prod_def zero_prod_def by simp

lemma zero_prod_least2 [simp]: "meet_prod x zero_prod = zero_prod"
  unfolding meet_prod_def zero_prod_def by simp

definition "sd_prod x y = (fst x \<cdot> fst y, snd x \<squnion> \<alpha> (fst x) (snd y))"

lemma sd_prod_assoc: "sd_prod x (sd_prod y z) = sd_prod (sd_prod x y) z"
  unfolding sd_prod_def
  by (smt fstI l_monoid_module.m3 l_monoid_module_axioms m1 mult.assoc sndI sup.commute sup.left_commute)

lemma sd_prod_onel [simp]: "sd_prod one_prod x = x"
  unfolding sd_prod_def one_prod_def by simp

lemma sd_prod_oner [simp]: "sd_prod x one_prod = x"
  unfolding sd_prod_def one_prod_def by simp

lemma sd_prod_zerol [simp]: "sd_prod zero_prod x = zero_prod"
  unfolding sd_prod_def zero_prod_def by simp

lemma "sd_prod x zero_prod = zero_prod"
  (*nitpick*)
  oops

lemma sd_prod_distl: "sd_prod x (plus_prod y z) = plus_prod (sd_prod x y) (sd_prod x z)"
  unfolding sd_prod_def plus_prod_def by (simp add: distrib_left m3 sup_assoc sup_left_commute)

lemma sd_prod_distr: "sd_prod (plus_prod x y) z = plus_prod (sd_prod x z) (sd_prod y z)"
  unfolding sd_prod_def plus_prod_def by (simp add: m2 sup_assoc sup_left_commute)

end

context kleene_lattice_module
begin

definition "star_prod x = ((fst x)\<^sup>\<star>, \<alpha> ((fst x)\<^sup>\<star>) (snd x))"

lemma star_prod_unfoldl: "plus_prod one_prod (sd_prod x (star_prod x)) = star_prod x"
  unfolding star_prod_def plus_prod_def sd_prod_def one_prod_def
  by (metis (no_types, lifting) fst_conv inf_sup_aci(5) l_monoid_module.m4 l_monoid_module_axioms m1 m2 snd_conv star_unfoldl_eq sup_bot.right_neutral)

lemma star_prod_unfoldr: "star_prod x = plus_prod one_prod (sd_prod (star_prod x) x)"
  unfolding star_prod_def plus_prod_def sd_prod_def one_prod_def
  by simp

lemma star_prod_inductl: "le_prod (sd_prod x y) y \<Longrightarrow> le_prod (sd_prod (star_prod x) y) y"
  unfolding le_prod_def sd_prod_def star_prod_def
  using m6 by auto

lemma star_prod_inductr: "le_prod (sd_prod y x) y \<Longrightarrow> le_prod (sd_prod y (star_prod x)) y"
  unfolding le_prod_def sd_prod_def star_prod_def
  by (metis (no_types, lifting) conway.dagger_plus_one distrib_left fst_conv join.sup.orderE m1 mult.right_neutral snd_conv star_inductr_var_equiv)

end

context cylindric_kleene_lattice_module
begin

definition "cyl_prod i x = (cyl i (fst x), \<alpha> (cyl i 1) (snd x))"

lemma cyl_prod_prop: "cyl i (fst x) = cyl i 1 \<cdot> (fst x) \<cdot> cyl i 1 \<Longrightarrow> cyl_prod i x = sd_prod (cyl i 1, \<bottom>) (sd_prod x (cyl i 1, \<bottom>))"
  unfolding cyl_prod_def sd_prod_def by (simp add: mult.assoc)

end

context liberation_kleene_lattice_module
begin

lemma l1_prod: "sd_prod (lib i, \<bottom>) zero_prod = zero_prod"
  unfolding sd_prod_def zero_prod_def by simp

lemma l2_prod: "le_prod one_prod (lib i, \<bottom>::'c::bounded_lattice_bot)"
  unfolding le_prod_def one_prod_def by (simp add: l2)

lemma l3_prod: 
  assumes "\<alpha> (lib i) (p \<sqinter> \<alpha> (lib i) q) = \<alpha> (lib i) p \<sqinter> \<alpha> (lib i) q"
  shows "sd_prod (lib i,\<bottom>) (meet_prod (x,p) (sd_prod (lib i,\<bottom>) (y,q))) = meet_prod (sd_prod (lib i,\<bottom>) (x,p)) (sd_prod (lib i,\<bottom>) (y,q))" 
  unfolding sd_prod_def meet_prod_def by (simp add: assms l3)

lemma l4_prod: "sd_prod (meet_prod (x,p) (sd_prod (y,q) (lib i,\<bottom>))) (lib i,\<bottom>) = meet_prod (sd_prod (x,p) (lib i,\<bottom>)) (sd_prod (y,q) (lib i,\<bottom>))"  
  unfolding sd_prod_def meet_prod_def by (simp add: l4)

lemma l5_prod: "sd_prod (lib i,\<bottom>) (lib j,\<bottom>) = sd_prod (lib j,\<bottom>) (lib i,\<bottom>)"
  unfolding sd_prod_def by (simp add: l5)

lemma l6_prod: "i \<noteq> i \<Longrightarrow> meet_prod (lib i,\<bottom>) (lib j,\<bottom>) = one_prod"
  unfolding meet_prod_def one_prod_def by simp

lemma l7_prod: "sd_prod (lib (i::'a),\<bottom>) (meet_prod (lib j,\<bottom>) (lib k,\<bottom>)) = meet_prod (sd_prod (lib i,\<bottom>) (lib j,\<bottom>)) (sd_prod (lib i,\<bottom>) (lib k,\<bottom>))" 
  unfolding sd_prod_def meet_prod_def by (simp add: l7)

lemma l8_prod: "sd_prod (meet_prod (lib i,\<bottom>) (lib j,\<bottom>)) (lib k,\<bottom>) = meet_prod (sd_prod (lib i,\<bottom>) (lib k,\<bottom>)) (sd_prod (lib j,\<bottom>) (lib k,\<bottom>))" 
  unfolding sd_prod_def meet_prod_def by (simp add: l8)

end

end