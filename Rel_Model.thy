section \<open>Relational Model of Cylindric Kleene and Liberation Lattices\<close>

theory Rel_Model
  imports Main 

begin

type_synonym ('a,'b) crel = "('a \<Rightarrow> 'b) rel" 

notation relcomp (infixl ";" 75)

lemma relcomp_def: "(a,b) \<in> R ; S = (\<exists>c. (a,c) \<in> R \<and> (c,b) \<in> S)"
  by blast

lemma subid_meet_distl: "P \<subseteq> Id \<Longrightarrow> P ; (R \<inter> S) = P ; R \<inter> P ; S"
  by blast

lemma subid_meet_distr: "P \<subseteq> Id \<Longrightarrow> (R \<inter> S) ; P = R ; P \<inter> S ; P"
  by blast

text \<open>First we define equality up to variable i and prove properties.\<close>

definition eq_upto :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "eq_upto i f g = (\<forall>j. i \<noteq> j \<longrightarrow> f j = g j)" 

lemma eq_upto_ref: "eq_upto i f f"
  unfolding eq_upto_def by simp

lemma eq_upto_sym: "eq_upto i f g = eq_upto i g f"
  unfolding eq_upto_def by force

lemma eq_upto_trans: "eq_upto i f g \<Longrightarrow> eq_upto i g h \<Longrightarrow> eq_upto i f h"
  unfolding eq_upto_def by force

lemma eq_upto_Id: "i \<noteq> j \<Longrightarrow> (eq_upto i f g \<and> eq_upto j f g) = (f = g)"
  unfolding eq_upto_def by force

lemma eq_upto_fun: "(\<forall>k. k \<noteq> i \<and> k \<noteq> j \<longrightarrow> a k = b k) \<Longrightarrow> \<exists>c.\<forall>k. (k \<noteq> i \<longrightarrow> a k = c k) \<and> (k \<noteq> j \<longrightarrow> c k = b k)"
proof- 
  fix k
  assume h1: "\<forall>k. k \<noteq> i \<and> k \<noteq> j \<longrightarrow> a k = b k"
  hence "\<exists>c. c = (\<lambda>k. if k = i then b k else a k) \<and> (\<forall>k. (k \<noteq> i \<longrightarrow> a k = c k) \<and> (k \<noteq> j \<longrightarrow> c k = b k))"
    by simp
  thus "\<exists>c.\<forall>k. (k \<noteq> i \<longrightarrow> a k = c k) \<and> (k \<noteq> j \<longrightarrow> c k = b k)"
    by metis 
qed
    
lemma eq_upto_comm: "(\<exists>c. eq_upto i a c \<and> eq_upto j c b) = (\<exists>c. eq_upto j a c \<and> eq_upto i c b)"
proof-
  have "(\<exists>c. eq_upto i a c \<and> eq_upto j c b) = (\<exists>c.\<forall>k. (k \<noteq> i \<longrightarrow> a k = c k) \<and> (k \<noteq> j \<longrightarrow> c k = b k))"
    unfolding eq_upto_def by auto
  also have "... = (\<forall>k. k \<noteq> i \<and> k \<noteq> j \<longrightarrow> a k = b k)"
    by (auto simp: eq_upto_fun)
  also have "... = (\<exists>c.\<forall>k. (k \<noteq> j \<longrightarrow> a k = c k) \<and> (k \<noteq> i \<longrightarrow> c k = b k))"
    by (auto simp: eq_upto_fun)
  also have "... = (\<exists>c. eq_upto j a c \<and> eq_upto i c b)"
    unfolding eq_upto_def by auto
  finally show ?thesis.
qed

definition eq_uptop :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where 
  "eq_uptop i fp gp = (\<forall>j. i \<noteq> j \<longrightarrow> ((fst fp) j = (fst gp) j \<and> (snd fp) j = (snd gp) j))" 

lemma eq_uptop_upto [simp]: "eq_uptop i (f,g) (h,k) = (eq_upto i f h \<and> eq_upto i g k)"
  unfolding eq_uptop_def eq_upto_def by force

lemma eq_uptop_ref: "eq_uptop i (f,g) (f,g)"
  unfolding eq_uptop_upto by (simp add: eq_upto_ref)

lemma eq_uptop_sym: "eq_uptop i (f,g) (h,k) = eq_uptop i (h,k) (f,g)"
  unfolding eq_uptop_upto by (simp add: eq_upto_sym)

lemma eq_uptop_trans: "eq_uptop i (f,g) (h,k) \<Longrightarrow> eq_uptop i (h,k) (l,m) \<Longrightarrow> eq_uptop i (f,g) (l,m)"
  unfolding eq_uptop_upto by (meson eq_upto_trans) 

text \<open>Next we define relational cylindrification.\<close>

definition cyl :: "'a \<Rightarrow> ('a,'b) crel \<Rightarrow> ('a,'b) crel" where
  "cyl i R = {(f,g). \<exists>h k. (\<forall>j. i \<noteq> j \<longrightarrow> (f j = h j \<and> g j = k j)) \<and> (h,k) \<in> R}" 

lemma cyl_eq_uptop1: "cyl i R = {fp. \<exists>gp. eq_uptop i fp gp \<and> gp \<in> R}"
  unfolding cyl_def eq_uptop_def by (safe, auto)

lemma cyl_eq_uptop2: "cyl i R = {(f,g). \<exists>h k. eq_uptop i (f,g) (h,k) \<and> (h,k) \<in> R}"
  unfolding cyl_def eq_uptop_def by simp

lemma cyl_Id: "cyl i Id = {(f,g). eq_upto i f g}"
  unfolding cyl_def Id_def eq_upto_def by fastforce

lemma cyl_Id_var: "(a,b) \<in> cyl i Id = eq_upto i a b"
  by (simp add: cyl_Id)

lemma cyl_id_rel: "cyl i Id ; R = {(a,b). \<exists>c. eq_upto i a c \<and> (c,b) \<in> R}"
proof-
  {fix a b
  have "(a,b) \<in> cyl i Id ; R = (\<exists>c. (a,c) \<in> cyl i Id \<and> (c,b) \<in> R)"
    by force
  also have "... = (\<exists>c. eq_upto i a c \<and> (c,b) \<in> R)"
    unfolding cyl_Id by simp
  finally have "(a,b) \<in> cyl i Id ; R = (\<exists>c. eq_upto i a c \<and> (c,b) \<in> R)".}
  thus ?thesis
    by blast
qed

lemma rel_cyl_id: "R ; cyl i Id = {(a,b). \<exists>c. (a,c) \<in> R \<and> eq_upto i c b}"
proof-
  {fix a b
  have "(a,b) \<in> R ; cyl i Id  = (\<exists>c. (a,c) \<in> R \<and> (c,b) \<in> cyl i Id)"
    by force
  also have "... = (\<exists>c. (a,c) \<in> R \<and> eq_upto i c b)"
    unfolding cyl_Id by simp
  finally have "(a,b) \<in> R ; cyl i Id = (\<exists>c. (a,c) \<in> R \<and> eq_upto i c b)".}
  thus ?thesis
    by blast
qed

text \<open>We prove the fundamental identity of relational cylindrification and cylindrification of the identity.\<close>

lemma cyl_Id_rep: "cyl i R = cyl i Id ; R ; cyl i Id"
proof-
  {fix a b
  have "(a,b) \<in> cyl i Id ; R ; cyl i Id = (\<exists>c d. (a,c) \<in> cyl i Id \<and> (c,d) \<in> R \<and> (d,b) \<in> cyl i Id)"
    by blast
  also have "... = (\<exists>c d. eq_upto i a c \<and> (c,d) \<in> R \<and> eq_upto i d b)"
    unfolding cyl_Id by simp
  also have "... = (\<exists>c d. eq_uptop i (a,b) (c,d) \<and> (c,d) \<in> R)"
    by (meson eq_upto_sym eq_uptop_upto)
  also have "... = ((a,b) \<in> cyl i R)"
    by (simp add: cyl_eq_uptop2)
  finally have "(a,b) \<in> cyl i Id ; R ; cyl i Id = ((a,b) \<in> cyl i R)".}
  thus ?thesis
    by force
qed

text \<open>We derive the axioms of liberation l-monoids by using this fundamental identity.\<close>

lemma cyl_Id_emp [simp]: "cyl i Id ; {} = {}"
  by simp

lemma Id_cyl_Id: "Id \<subseteq> cyl i Id"
  using cyl_eq_uptop1 eq_uptop_ref by fastforce

lemma cyl_Id_inter: "cyl i Id ; (R \<inter> cyl i Id ; S) = cyl i Id ; R \<inter> cyl i Id ; S"
proof-
  {fix a b
    have "(a,b) \<in> cyl i Id ; (R \<inter> cyl i Id ; S) = (\<exists>c. eq_upto i a c \<and> (c,b) \<in> R \<and> (\<exists>d. eq_upto i c d \<and> (d,b) \<in> S))"
      unfolding cyl_Id by force
    also have "... = (\<exists>c. eq_upto i a c \<and> (c,b) \<in> R \<and> (\<exists>d. eq_upto i a d \<and> (d,b) \<in> S))"
      by (meson eq_upto_sym eq_upto_trans)
    also have "... = ((a,b) \<in> cyl i Id ; R \<inter> cyl i Id ; S)"
      by (smt Int_Collect cyl_id_rel mem_Collect_eq prod.simps(2))
    finally have "((a,b) \<in> cyl i Id ; (R \<inter> cyl i Id ; S)) = ((a,b) \<in> cyl i Id ; R \<inter> cyl i Id ; S)"
      by blast}
  thus ?thesis
    by blast
qed

lemma inter_cyl_Id: "(R \<inter> S; cyl i Id) ; cyl i Id = R ; cyl i Id \<inter> S ; cyl i Id"
proof-
  {fix a b
    have "(a,b) \<in> (R \<inter> S; cyl i Id) ; cyl i Id = (\<exists>c. (a,c) \<in> R \<and> (\<exists>d. (a,d) \<in> S \<and> eq_upto i d c) \<and> eq_upto i c b)"
      unfolding cyl_Id by force
    also have "... = (\<exists>c. (a,c) \<in> R \<and> (\<exists>d. (a,d) \<in> S \<and> eq_upto i d b) \<and> eq_upto i c b)"
      by (meson eq_upto_sym eq_upto_trans)
    also have "... = ((a,b) \<in> R ; cyl i Id \<inter> S ; cyl i Id)"
      by (smt Int_iff mem_Collect_eq rel_cyl_id split_conv)
    finally have "(a,b) \<in> (R \<inter> S; cyl i Id) ; cyl i Id = ((a,b) \<in> R ; cyl i Id \<inter> S ; cyl i Id)"
      by blast}
  thus ?thesis
    by blast
qed

lemma cyl_Id_idem [simp]: "cyl i Id ; cyl i Id = cyl i Id"
  by (metis R_O_Id cyl_Id_rep)

lemma cyl_Id_comm: "cyl i Id ; cyl j Id = cyl j Id ; cyl i Id"
proof- 
  {fix a b :: "'a \<Rightarrow> 'b"
  have "(a,b) \<in> cyl i Id ; cyl j Id = (\<exists>c. eq_upto i a c \<and> eq_upto j c b)"
    by (simp add: cyl_Id relcomp.simps)
  also have "... = (\<exists>c. eq_upto j a c \<and> eq_upto i c b)"
    by (simp add: eq_upto_comm)
  also have "... = ((a,b) \<in> cyl j Id ; cyl i Id)"
    by (simp add: cyl_Id relcomp.simps)
  finally have "(a,b) \<in> cyl i Id ; cyl j Id = ((a,b) \<in> cyl j Id ; cyl i Id)".}
  thus ?thesis
    by blast
qed

lemma cyl_Id_Id: "i \<noteq> j \<Longrightarrow> cyl i Id \<inter> cyl j Id = Id"
proof-
  assume h: "i \<noteq> j"
  {fix a b :: "'a \<Rightarrow> 'b"
  have "(a,b) \<in> cyl i Id \<inter> cyl j Id = (eq_upto i a b \<and> eq_upto j a b)"
    unfolding cyl_Id by simp
  also have "... = (a = b)"
    by (simp add: eq_upto_Id h)
  finally have "(a,b) \<in> cyl i Id \<inter> cyl j Id = ((a,b) \<in> Id)"
    by simp}
  thus ?thesis
    by force
qed

lemma cyl_Id_inter_distl: "cyl i Id ; (cyl j Id \<inter> cyl k Id) = cyl i Id ; cyl j Id \<inter> cyl i Id ; cyl k Id"
proof-
  {fix a b :: "'a \<Rightarrow> 'b"
  have "(a,b) \<in> cyl i Id ; (cyl j Id \<inter> cyl k Id) = (\<exists>c. eq_upto i a c \<and> eq_upto j c b \<and> eq_upto k c b)"
    unfolding relcomp_def cyl_Id by simp
  also have "... = ((\<exists>c. eq_upto i a c \<and> eq_upto j c b) \<and> (\<exists>c. eq_upto i a c \<and> eq_upto k c b))"
    by (smt eq_upto_def)
  also have "... = ((a,b) \<in> cyl i Id ; cyl j Id \<inter> cyl i Id ; cyl k Id)"
    unfolding relcomp_def cyl_Id by force
  finally have "(a,b) \<in> cyl i Id ; (cyl j Id \<inter> cyl k Id) = ((a,b) \<in> cyl i Id ; cyl j Id \<inter> cyl i Id ; cyl k Id)".}
  thus ?thesis
    by force
qed

lemma cyl_Id_inter_disrl: "(cyl i Id \<inter> cyl j Id) ; cyl k Id = cyl i Id ; cyl k Id \<inter> cyl j Id ; cyl k Id"
proof-
  {fix a b :: "'a \<Rightarrow> 'b"
  have "(a,b) \<in> (cyl i Id \<inter> cyl j Id) ; cyl k Id = (\<exists>c. eq_upto i a c \<and> eq_upto j a c \<and> eq_upto k c b)"
    unfolding relcomp_def cyl_Id by simp
  also have "... = ((\<exists>c. eq_upto i a c \<and> eq_upto k c b) \<and> (\<exists>c. eq_upto j a c \<and> eq_upto k c b))"
    by (smt eq_upto_def)
  also have "... = ((a,b) \<in> cyl i Id ; cyl k Id \<inter> cyl j Id ; cyl k Id)"
    unfolding relcomp_def cyl_Id by force
  finally have "(a,b) \<in> (cyl i Id \<inter> cyl j Id) ; cyl k Id = ((a,b) \<in> cyl i Id ; cyl k Id \<inter> cyl j Id ; cyl k Id)".}
  thus ?thesis
    by force
qed

text \<open>Finally we provide three counterexamples and provide a relationship that is used in the definition of assignments.\<close>

lemma "cyl i Id ; cyl j Id = cyl i Id \<union> cyl j Id"
  (*nitpick*)
  oops

lemma "trancl (cyl i Id \<union> cyl j Id) = (cyl i Id \<union> cyl j Id)"
  (*nitpick*)
  oops

lemma "cyl i Id \<union> cyl j Id \<subseteq> cyl i Id ; cyl j Id"
  using Id_cyl_Id by fastforce

lemma "P \<subseteq> Id \<Longrightarrow> cyl i Id ; (cyl i P \<inter> Id) = cyl i P"
  by (smt Id_cyl_Id O_assoc R_O_Id cyl_Id_inter cyl_Id_rep dual_order.trans inf.orderE inf_commute inter_cyl_Id)

lemma "cyl i Id ; (cyl i R \<inter> Id) = cyl i R"
  (*nitpick*)
  oops

lemma "cyl i Id = Id"
  (*nitpick*)
  oops

lemma cyl_Id_comp: "cyl i (cyl j Id) = cyl i Id ; cyl j Id"
proof- 
  have "cyl i (cyl j Id) = cyl i Id ; cyl j Id ; cyl i Id"
    by (meson cyl_Id_rep)
  also have "... = cyl i Id ; cyl i Id ; cyl j Id"
    by (metis O_assoc cyl_Id_comm)
  also have "... = cyl i Id ; cyl j Id"
    by simp
  finally show ?thesis.
qed

lemma cyl_Id_interp: "cyl i (cyl j Id \<inter> cyl k Id) = (cyl i Id ; cyl j Id) \<inter> (cyl i Id ; cyl k Id)"
  by (metis R_O_Id cyl_Id_Id cyl_Id_comp cyl_Id_inter_distl inf.idem)


text \<open>We prove a property of frames.\<close>

lemma "R \<inter> cyl i Id = {(a,b) \<in> R. \<exists>c. a = fun_upd b i c}"
  unfolding cyl_def Id_def fun_upd_def by force

lemma cyl_Id_meet_pres: "cyl i Id ; cyl j Id \<inter> cyl i Id ; cyl k Id \<subseteq> cyl i (cyl j Id \<inter> cyl k Id)"
  by (metis R_O_Id cyl_Id_Id cyl_Id_comp cyl_Id_inter_distl inf.idem set_eq_subset)

end