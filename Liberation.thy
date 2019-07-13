section \<open>Liberation\<close>

theory Liberation
  imports Main  "~~/src/HOL/Library/Lattice_Syntax" 

begin

notation times (infixl "\<cdot>" 70)

locale cylindric_algebra =
  fixes cyl :: "'a \<Rightarrow> 'b::boolean_algebra \<Rightarrow> 'b::boolean_algebra"
  and dia :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes c1 [simp]: "cyl i \<bottom> = \<bottom>"
  and c2: "x \<le> cyl i x"
  and c3: "cyl i (x \<sqinter> cyl i y) = cyl i x \<sqinter> cyl i y"
  and c4: "cyl i (cyl j x) = cyl j (cyl i x)"
  and c5 [simp]: "dia i i = \<top>"
  and c6: "i \<noteq> j \<Longrightarrow> i \<noteq> k \<Longrightarrow> d j k = cyl i (dia j i \<sqinter> dia i k)"
  and c7: "i \<noteq> j \<Longrightarrow> cyl i (dia i j \<sqinter> x) \<sqinter> cyl i (dia i j \<sqinter> -x) = \<bottom>"

begin

lemma cyl_idem [simp]: "cyl i (cyl i x) = cyl i x"
  by (metis c2 c3 inf_top.left_neutral top.extremum_uniqueI)

lemma c3_var [simp]: "cyl i (cyl i x \<sqinter> cyl i y) = cyl i x \<sqinter> cyl i y"
  by (simp add: c3)

lemma cyl_iso: "x \<le> y \<Longrightarrow> cyl i x \<le> cyl i y"
  by (metis c2 c3 inf.order_iff le_infI2)

lemma cyl_top [simp]: "cyl i \<top> = \<top>"
  by (simp add: antisym c2)

lemma cyl_very_strict: "(cyl i x = \<bottom>) = (x = \<bottom>)"
  by (metis bot.extremum_unique c1 c2)

lemma cyl_conjugate: "(cyl i x \<sqinter> y = \<bottom>) = (x \<sqinter> cyl i y = \<bottom>)"
  by (metis c3 cyl_very_strict inf_aci(1))

lemma cyl_compl1 [simp]: "cyl i (-cyl i x) = -cyl i x"
  by (metis c2 compl_unique cyl_conjugate cyl_idem inf_compl_bot le_iff_sup sup_compl_top_left2)

lemma cyl_compl2: "(cyl i x = x) = (cyl i (-x) = -x)"
  by (metis cyl_compl1 double_compl)

lemma cyl_join_pres_aux [simp]: "cyl i (cyl i x \<squnion> cyl i y) = cyl i x \<squnion> cyl i y"
  by (metis (no_types, lifting) c3 compl_sup cyl_compl1 cyl_compl2)

lemma cyl_join_pres: "cyl i (x \<squnion> y) = cyl i x \<squnion> cyl i y"
  by (smt c2 c3 cyl_join_pres_aux inf.order_iff inf_aci(1) inf_aci(2) inf_sup_distrib2 sup_ge1 sup_ge2)

lemma "i \<noteq> j \<Longrightarrow> cyl i x \<noteq> cyl j x"
  (*nitpick*)
  oops

lemma cyl_dia1: "i \<noteq> j \<Longrightarrow> i \<noteq> k \<Longrightarrow> cyl i (dia j k) = dia j k"
  by (simp add: c6)

lemma dia_sym_var: "i \<noteq> j \<Longrightarrow> dia i j = dia j i"
  by (smt c5 c6 compl_bot_eq compl_inf compl_unique cylindric_algebra.c7 cylindric_algebra.cyl_very_strict cylindric_algebra_axioms double_compl inf_sup_aci(1) inf_top.monoid_axioms monoid.right_neutral)

lemma dia_sym: "dia i j = dia j i"
  using dia_sym_var by force

lemma dia_cyl_top [simp]: "cyl i (dia i j) = \<top>"
  by (metis (mono_tags, hide_lams) c5 c6 cyl_top dia_sym inf.idem)

lemma dia_meet1: "i \<noteq> j \<Longrightarrow> dia i j \<sqinter> cyl i (dia i j \<sqinter> x) \<le> x"
proof-
  assume "i \<noteq> j"
  hence "cyl i (dia i j \<sqinter> x) \<sqinter> cyl i (dia i j \<sqinter> -x) = \<bottom>"
    by (simp add: c7)
  hence "cyl i (cyl i (dia i j \<sqinter> x)) \<sqinter> dia i j \<sqinter> -x = \<bottom>"
    by (simp add: cyl_conjugate inf_assoc)
  hence "cyl i (dia i j \<sqinter> x) \<sqinter> dia i j \<sqinter> -x = \<bottom>"
    by (simp add: cyl_idem)
  thus ?thesis
    by (smt abel_semigroup.commute inf.abel_semigroup_axioms inf.absorb_iff2 inf_compl_bot_right inf_sup_distrib1 inf_top.right_neutral sup_compl_top sup_inf_absorb)
qed

lemma dia_meet2: "i \<noteq> j \<Longrightarrow> cyl i (dia i j \<sqinter> x \<sqinter> y) = cyl i (dia i j \<sqinter> x) \<sqinter> cyl i (dia i j \<sqinter> y)"
  by (smt c2 c3 dia_meet1 inf.order_iff inf_aci(1) inf_aci(2))

definition subst :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
  "subst i j x = (if i = j then x else cyl i (dia i j \<sqinter> x))"

lemma subst_join: "subst i j (x \<squnion> y) = subst i j x \<squnion> subst i j y"
  by (simp add: cyl_join_pres inf_sup_distrib1 subst_def)

lemma subst_compl: "- (subst i j x) = subst i j (-x)"
  by (smt c7 compl_inf_bot compl_sup_top compl_unique cyl_join_pres dia_cyl_top inf_commute inf_sup_distrib2 inf_top.right_neutral subst_def)

lemma subst_top [simp]: "subst i j \<top> = \<top>"
  by (simp add: subst_def)

lemma subst_meet_var: "i \<noteq> j \<Longrightarrow> subst i j (x \<sqinter> y) = subst i j x \<sqinter> subst i j y"
  by (metis (no_types, lifting) dia_meet2 inf.assoc subst_def)

lemma subst_meet: "subst i j (x \<sqinter> y) = subst i j x \<sqinter> subst i j y"
  by (metis (no_types, lifting) dia_meet2 inf_assoc subst_def)

lemma subst_dia: "i \<noteq> k \<Longrightarrow> subst i j (dia i k) = dia j k"
  by (simp add: c6 dia_sym subst_def)

lemma subst_dia2: "i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> subst i j (dia k l) = dia k l"
  by (simp add: c3 c6 subst_def)

lemma subst_dia_meet: "i \<noteq> j \<Longrightarrow> i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> i \<noteq> m \<Longrightarrow> j \<noteq> k \<Longrightarrow> j \<noteq> l \<Longrightarrow> j \<noteq> m \<Longrightarrow> k \<noteq> l \<Longrightarrow> k \<noteq> m \<Longrightarrow> l \<noteq> m \<Longrightarrow> subst i j (dia i k \<sqinter> dia l m) = dia j k \<sqinter> dia l m"
proof -
  assume a1: "i \<noteq> j"
assume a2: "i \<noteq> k"
assume a3: "l \<noteq> m"
assume a4: "i \<noteq> l"
assume a5: "i \<noteq> m"
have f6: "\<forall>f fa a aa. \<not> cylindric_algebra f fa \<or> (a::'a) = aa \<or> (fa a aa::'b) = fa aa a"
by (meson cylindric_algebra.dia_sym_var)
then have f7: "dia l m = dia m l"
  using a3 cylindric_algebra_axioms by blast
have f8: "dia i j = dia j i"
  using f6 a1 cylindric_algebra_axioms by blast
  have f9: "dia j k = cyl i (dia j i \<sqinter> dia i k)"
    using a2 a1 by (meson c6)
have "cyl i (dia m l) = dia m l"
  using a5 a4 by (meson cyl_dia1)
  then have "cyl i (dia i j \<sqinter> dia m l) = dia m l"
by (metis (no_types) c3 dia_cyl_top inf_aci(1) inf_top.monoid_axioms monoid.right_neutral)
  then show ?thesis
    using f9 f8 f7 a1 by (metis (no_types) dia_meet2 inf_assoc subst_def)
qed

end

end