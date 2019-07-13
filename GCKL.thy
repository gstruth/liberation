section \<open>Generalised Cylindric Kleene Lattices\<close>

text \<open>Using this mathematical component requires downloading the Archive of Formal Proofs.\<close>

theory GCKL
  imports CKL2

begin

primrec list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_inter [] ys = []" |
  "list_inter (x # xs) ys = (let zs = list_inter xs ys in (if x \<in> set ys then x # zs else zs))"

lemma list_set_inter: "set (list_inter ks ls) = set ks \<inter> set ls"
  by (induct ks, simp_all, metis (full_types) Int_insert_left list.simps(15))


context cylindric_l_monoid_zerol
begin

primrec cyl_list :: "('a::linorder) list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "cyl_list [] x = x" |
  "cyl_list (i # is) x = cyl i (cyl_list is x)"

lemma cyl_list_nil_fun [simp]: "cyl_list [] = id"
  unfolding fun_eq_iff by simp

lemma cyl_list_append: "cyl_list ks (cyl_list ls x) = cyl_list (ks @ ls) x"
  by (induct ks, simp_all)

lemma cyl_list_cons_fun: "cyl_list (l # ls) = cyl l \<circ> cyl_list ls"
  unfolding fun_eq_iff comp_def by simp
  
lemma setmem_cyl: "l \<in> set ls \<Longrightarrow> cyl_list (l # ls) x = cyl_list ls x"
  by (induct ls, simp_all, metis cyl_comm cyl_fix_im)

lemma cyl_list_remdups: "cyl_list (remdups ls) x = cyl_list ls x"
  apply (induct ls)
  using setmem_cyl by auto

lemma cyl_list_el_comm: "cyl_list ls (cyl i x) = cyl i (cyl_list ls x)"
  by (induct ls, simp_all add: cyl_comm)

lemma cyl_sorted_aux: "sorted ls \<Longrightarrow> cyl i (cyl_list ls x) = cyl_list (insort i ls) x"
  by (induct ls, simp_all add: cyl_comm)

lemma cyl_sorted: "cyl i (cyl_list (sort ls) x) = cyl_list (insort i (sort ls)) x"
  by (simp add: cyl_sorted_aux)

lemma cyl_list_sort: "cyl_list ls x = cyl_list (sort ls) x"
  by (induct ls, simp_all add: cyl_sorted)

definition cyl_set :: "('a::linorder) set \<Rightarrow> 'b \<Rightarrow> 'b" where
  "cyl_set X x = cyl_list (sorted_list_of_set X) x"

lemma cyl_list_set: "cyl_list ls x = cyl_set (set ls) x"
  unfolding cyl_set_def by (metis cyl_list_remdups cyl_list_sort sorted_list_of_set_sort_remdups)

lemma cyl_list_set_eq: "set ks = set ls \<Longrightarrow> cyl_list ks x = cyl_list ls x"
  by (simp add: cyl_list_set)

lemma cyl_list_iso_aux: "cyl_list ls x \<le> cyl_list (ks @ ls) x"
  by (induct ks, simp_all, meson cyl_ext order_trans)

lemma cyl_list_iso: "set ks \<subseteq> set ls \<Longrightarrow> cyl_list ks x \<le> cyl_list ls x"
  by (metis UnCI Un_Int_distrib cyl_list_set cylindric_l_monoid_zerol.cyl_list_iso_aux cylindric_l_monoid_zerol_axioms inf.commute inf.orderE set_append subsetI sup.idem)

lemma "cyl_list ks x \<le> cyl_list ls x \<Longrightarrow> set ks \<subseteq> set ls"
  (*nitpick*)
  oops
 
lemma cyl_list_idem [simp]: "cyl_list ls (cyl_list ls x) = cyl_list ls x"
  using cyl_list_append cyl_list_set by auto

lemma cyl_list_one_cons: "cyl i 1 \<cdot> cyl_list ls 1 = cyl_list (i # ls) 1"
  apply (induct ls)
   apply simp_all
  by (smt cyl_1_unl cyl_comm cyl_id_seq_eq cyl_oplax cyl_rel_prop_var1 join.le_iff_sup join.sup.order_iff mult.assoc)

lemma cyl_list_one_app: "cyl_list ks 1 \<cdot> cyl_list ls 1 = cyl_list (ks @ ls) 1"
  by (induct ks, simp_all, metis cyl_list.simps(2) cyl_list_one_cons mult.assoc)

lemma "i \<noteq> j \<Longrightarrow> cyl_list (ls @ [i]) 1 \<sqinter> cyl_list (ls @ [j]) 1 = cyl_list ls 1"
  oops

lemma "i \<noteq> j \<Longrightarrow> cyl_list ([i] @ ls) 1 \<sqinter> cyl_list ([j] @ ls) 1 = cyl_list ls 1"
  oops

lemma rect_id: "cyl_list ks 1 \<sqinter> cyl_list ls 1 = cyl_list (list_inter ks ls) 1"
  oops

lemma c1_list [simp]: "cyl_list ls 0 = 0"
  by (induct ls, simp_all)

lemma c2_list: "x \<le> cyl_list ls x"
  apply (induct ls)
   apply simp_all
  using cyl_ext dual_order.trans by blast

lemma c3_list: "cyl_list ls (x + y) = cyl_list ls x + cyl_list ls y"
  by (induct ls, simp_all add: cyl_sup_add)

lemma c4_list: "\<forall>x y. cyl_list ls (x \<sqinter> cyl_list ls y) = cyl_list ls x \<sqinter> cyl_list ls y"
  by (induct ls, simp_all, metis cyl_inf cyl_list_el_comm)

lemma c5_list: "cyl_list ks (cyl_list ls x) = cyl_list ls (cyl_list ks x)" 
  by (induct ls, simp_all add: cyl_list_el_comm)

lemma c5_list_var: "cyl_list (ks @ ls) x = cyl_list (ls @ ks) x"
  using c5_list cyl_list_append by auto 

lemma c6_list: "\<forall>x y. cyl_list ls (x \<cdot> cyl_list ls y) = cyl_list ls x \<cdot> cyl_list ls y"
  by (induct ls, simp_all, metis cyl_list_el_comm cyl_multr)

lemma c7_list: "\<forall>x y. cyl_list ls (cyl_list ls x \<cdot> y) = cyl_list ls x \<cdot> cyl_list ls y"
  by (induct ls, simp_all, metis cyl_list_el_comm cyl_multl)

lemma c8_list: 
  assumes "cyl_list ks 1 \<sqinter> cyl_list ls 1 = cyl_list (list_inter ks ls) 1"
  shows "list_inter ks ls = [] \<Longrightarrow> cyl_list ks 1 \<sqinter> cyl_list ls 1 = 1"
  by (simp add: assms)

lemma c9_list:   
  assumes "\<forall>ks ls. cyl_list ks 1 \<sqinter> cyl_list ls 1 = cyl_list (list_inter ks ls) 1"
  shows"(cyl_list ks 1 \<cdot> cyl_list ls 1) \<sqinter> (cyl_list ks 1 \<cdot> cyl_list ms 1) = cyl_list ks (cyl_list ls 1 \<sqinter> cyl_list ms 1)"
  by (metis Un_Int_distrib cyl_list_append cyl_list_one_app cylindric_l_monoid_zerol.cyl_list_set assms cylindric_l_monoid_zerol_axioms list_set_inter set_append)

lemma c10_list: "cyl_list ks (cyl_list ls 1) = cyl_list ks 1 \<cdot> cyl_list ls 1"
  by (simp add: cyl_list_append cyl_list_one_app)

lemma cyl_list_id_absorb1: 
  assumes "\<forall>ks ls. cyl_list ks 1 \<sqinter> cyl_list ls 1 = cyl_list (list_inter ks ls) 1"
  shows "cyl_list ks 1 \<cdot> (cyl_list ks 1 \<sqinter> cyl_list ls 1) = cyl_list ks 1"
  by (metis (no_types, lifting) assms c10_list c2_list c4_list c5_list inf.commute inf_absorb2)

lemma cyl_list_id_absorb2: 
  assumes "\<forall>ks ls. cyl_list ks 1 \<sqinter> cyl_list ls 1 = cyl_list (list_inter ks ls) 1"
  shows "cyl_list ks 1 \<sqinter> (cyl_list ks 1 \<cdot> cyl_list ls 1) = cyl_list ks 1"
  by (metis (no_types, lifting) assms c10_list c2_list c4_list c5_list inf.commute inf_absorb2)

end

context cylindric_kleene_lattice_zerol
begin

lemma c11_list: "cyl_list ls (x\<^sup>\<oplus>) \<le> (cyl_list ls x::'b::{l_monoid_zerol,kleene_algebra_zerol})\<^sup>\<oplus>"
  by (induct ls, simp_all, metis cyl_iso cyl_kplus cyl_list.simps(2) order_trans)

lemma cyl_id_star_fix [simp]: "(cyl_list ls 1)\<^sup>\<star> = cyl_list ls 1"
  by (metis c2_list c7_list cyl_list_idem mult.right_neutral star_inductr_var_eq2 sup_id_star1)

lemma cyl_id_plus_fix [simp]: "(cyl_list ls 1)\<^sup>\<oplus> = cyl_list ls 1"
  by (metis c7_list cyl_list_idem kplus_def mult_oner star_inductr_var_eq2)

end

context cylindric_l_monoid_zerol
begin

text \<open>We define programs with frames\<close>

definition fprog :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
 "fprog ls x = x \<sqinter> cyl_list ls 1"

lemma fprog1: "fprog ls x \<le> x"
  by (simp add: fprog_def)

lemma fprog2: "set ks \<subseteq> set ls \<Longrightarrow> fprog ks x \<le> fprog ls x"
  unfolding fprog_def using cyl_list_iso inf_mono by blast

lemma fprog3: "x \<le> y \<Longrightarrow> fprog ls x \<le> fprog ls y"
  unfolding fprog_def using inf_mono by blast

lemma fprog4: "fprog ls x + fprog ls y \<le> fprog ls (x + y)"
  by (simp add: fprog3)

lemma fprog4_eq: 
  assumes "\<forall>x y z. (x + y) \<sqinter> (z::'b) = (x \<sqinter> y) + (x \<sqinter> z)"
  shows "fprog ls (x + y) = fprog ls x + fprog ls y"
  by (metis (no_types, lifting) add_idem' assms lmon_lat.inf_sup_absorb)

lemma fprog5: "fprog ls x \<cdot> fprog ls y \<le> fprog ls (x \<cdot> y)"
  unfolding fprog_def
  by (metis (no_types, lifting) cyl_list_idem cylindric_l_monoid_zerol.c10_list cylindric_l_monoid_zerol_axioms inf_le1 inf_le2 le_inf_iff mult_isol_var)

lemma fprog7: "x \<le> 1 \<Longrightarrow> fprog ls x = x"
  by (metis c2_list dual_order.trans fprog_def inf.orderE)

end

context cylindric_kleene_lattice_zerol
begin

lemma fprog6: "(fprog ls x)\<^sup>\<star> \<le> fprog ls (x\<^sup>\<star>)"
  by (metis cyl_id_star_fix fprog1 fprog_def inf_le2 le_inf_iff star_iso) 

lemma refine_skip: "1 \<le> x \<Longrightarrow> fprog ls 1 \<le> fprog ls x"
  by (simp add: fprog3)

lemma refine4: "y \<le> x \<Longrightarrow> fprog ls y \<le> x"
  using dual_order.trans fprog1 by blast

lemma refine_seq: "x \<cdot> y \<le> z \<Longrightarrow> fprog ls x \<cdot> fprog ls y \<le> fprog ls z"
  by (meson fprog3 fprog5 order_subst1)

lemma refine_cond: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<cdot> x + q \<cdot> y \<le> z \<Longrightarrow> p \<cdot> fprog ls x + q \<cdot> fprog ls y \<le> fprog ls z"
  using fprog7 refine_seq by fastforce

lemma refine_loop: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> (p \<cdot> x)\<^sup>\<star> \<cdot> q \<le> y \<Longrightarrow> (p \<cdot> fprog ls x)\<^sup>\<star> \<cdot> q \<le> fprog ls y"
proof-
  assume h1: "p \<le> 1"
  and h2: "q \<le> 1"
  and h3: "(p \<cdot> x)\<^sup>\<star> \<cdot> q \<le> y"
  hence "(p \<cdot> fprog ls x)\<^sup>\<star> \<cdot> q \<le> (fprog ls (p \<cdot> x)\<^sup>\<star>) \<cdot> q"
    by (metis fprog5 fprog7 h1 mult_isor star_iso)
  also have "... \<le> fprog ls ((p \<cdot> x)\<^sup>\<star> \<cdot> q)"
    by (smt cyl_id_star_fix cyl_list_idem cylindric_l_monoid_zerol.c10_list cylindric_l_monoid_zerol.fprog1 cylindric_l_monoid_zerol.fprog7 cylindric_l_monoid_zerol_axioms fprog_def h2 inf.absorb_iff2 inf_le2 le_inf_iff mult_isol_var star_iso)
  also have "... \<le> fprog ls y"
    by (simp add: fprog3 h3)
  finally show ?thesis.
qed

end

end