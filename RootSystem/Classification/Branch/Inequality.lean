import RootSystem.Classification.Branch.Energy
import RootSystem.Classification.NoCycle

variable {n : ℕ}

/-- A nonzero off-diagonal entry of a generalized Cartan matrix gives a "bond"
weight `√(C i j * C j i) ≥ 1`, since the product of the two nonzero nonpositive
integer entries is a positive integer. -/
lemma SymmMatrix_bond_ge_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) {i j : Fin n} (hij : i ≠ j) (hC : C i j ≠ 0) :
    (1 : ℝ) ≤ Real.sqrt (C i j * C j i) := by
  have hCji : C j i ≠ 0 := fun h => hC ((hGCM.vanish_symm j i).mp h)
  have h1 : (1 : ℤ) ≤ C i j * C j i := by
    have hi : C i j ≤ 0 := hGCM.off_diag_nonpos i j hij
    have hj : C j i ≤ 0 := hGCM.off_diag_nonpos j i hij.symm
    nlinarith [hi, hj, hC, hCji, mul_pos_of_neg_of_neg (lt_of_le_of_ne hi hC)
      (lt_of_le_of_ne hj hCji)]
  have : (1 : ℝ) ≤ ((C i j * C j i : ℤ) : ℝ) := by exact_mod_cast h1
  calc (1 : ℝ) = Real.sqrt 1 := by simp
    _ ≤ Real.sqrt (C i j * C j i) := by
        apply Real.sqrt_le_sqrt; exact_mod_cast this

/-! ### Linking the Dynkin graph to the combinatorial core -/

/-- The underlying simple-graph adjacency of `C`. -/
def Gadj (C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : Prop := i ≠ j ∧ C i j ≠ 0

instance (C : Matrix (Fin n) (Fin n) ℤ) : DecidableRel (Gadj C) := by
  intro i j; unfold Gadj; infer_instance

lemma Gadj_symm (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C) :
    ∀ i j, Gadj C i j → Gadj C j i := by
  rintro i j ⟨hij, hC⟩
  exact ⟨hij.symm, fun h => hC ((hGCM.vanish_symm j i).mp h)⟩

lemma Gadj_irr (C : Matrix (Fin n) (Fin n) ℤ) : ∀ i, ¬ Gadj C i i := by
  rintro i ⟨h, _⟩; exact h rfl

/-- Adjacency in the Dynkin diagram with the vertex `u` deleted: `a` and `b` are
adjacent, and neither of them is `u`. -/
def adjExcl (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (a b : Fin n) : Prop :=
  a ≠ b ∧ a ≠ u ∧ b ≠ u ∧ C a b ≠ 0

instance (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) : DecidableRel (adjExcl C u) := by
  intro a b; unfold adjExcl; infer_instance

/-- Reachability in the Dynkin diagram with the vertex `u` deleted. -/
def reachExcl (C : Matrix (Fin n) (Fin n) ℤ) (u v w : Fin n) : Prop :=
  Relation.ReflTransGen (adjExcl C u) v w

/-- The branch at `u` through `v`: all vertices reachable from `v` without
passing through `u`. -/
def branchSet (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : Set (Fin n) :=
  {w | reachExcl C u v w}

/-- The number of vertices in the branch at `u` through `v`. -/
noncomputable def branchSize (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : ℕ :=
  (branchSet C u v).ncard

/-- The branch at `u` through `v`, as a `Finset`. -/
noncomputable def branchFinset (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : Finset (Fin n) :=
  (branchSet C u v).toFinset

@[simp] lemma mem_branchFinset (C : Matrix (Fin n) (Fin n) ℤ) (u v w : Fin n) :
    w ∈ branchFinset C u v ↔ reachExcl C u v w := by
  simp [branchFinset, branchSet]

lemma branchSize_eq_card (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) :
    branchSize C u v = (branchFinset C u v).card := by
  rw [branchSize, branchFinset, Set.ncard_eq_toFinset_card']

lemma branchFinset_refl (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) :
    v ∈ branchFinset C u v := by
  rw [mem_branchFinset]
  apply Relation.ReflTransGen.refl

/-- A within-branch reachability path is a within-`branchFinset` path for the
simple-graph adjacency, hence the branch is connected from `v`. -/
lemma branch_connected (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) :
    ∀ w ∈ branchFinset C u v, reachIn (Gadj C) (branchFinset C u v) v w := by
  intro w hw
  rw [mem_branchFinset] at hw
  induction hw with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hva hab ih =>
      have ham : a ∈ branchFinset C u v := (mem_branchFinset C u v a).mpr hva
      have hbm : b ∈ branchFinset C u v := (mem_branchFinset C u v b).mpr (hva.tail hab)
      exact ih.tail ⟨ham, hbm, hab.1, hab.2.2.2⟩

/-- Each branch carries a nonnegative weighting with the rooted-energy bound. -/
lemma branch_marking (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (u v : Fin n) :
    ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, i ∉ branchFinset C u v → y i = 0) ∧
      (branchSize C u v : ℝ) / (branchSize C u v + 1) ≤
        2 * y v - 2 * (∑ i ∈ branchFinset C u v, (y i) ^ 2)
          + (∑ i ∈ branchFinset C u v, ∑ j ∈ branchFinset C u v,
              if Gadj C i j then y i * y j else 0) := by
  have hr : v ∈ branchFinset C u v := (mem_branchFinset C u v v).mpr Relation.ReflTransGen.refl
  obtain ⟨y, hy0, hsupp, _, hE⟩ :=
    branch_energy_strong (Gadj C) (Gadj_symm C hGCM) (Gadj_irr C) (branchFinset C u v) v hr
      (branch_connected C u v)
  refine ⟨y, hy0, hsupp, ?_⟩
  rw [branchSize_eq_card]
  exact hE

/-- Every vertex of a branch at `u` is different from `u`. -/
lemma reachExcl_ne_u (C : Matrix (Fin n) (Fin n) ℤ) (u v w : Fin n)
    (h : reachExcl C u v w) (hv : v ≠ u) : w ≠ u := by
  induction h with
  | refl => exact hv
  | tail _ hab _ => exact hab.2.2.1

lemma u_notMem_branch (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) (huv : v ≠ u) :
    u ∉ branchFinset C u v := by
  rw [mem_branchFinset]
  intro h
  exact reachExcl_ne_u C u v u h huv rfl

lemma neighbor_iff_Gadj (C : Matrix (Fin n) (Fin n) ℤ) (u i : Fin n) :
    i ∈ neighborSet C u ↔ Gadj C u i := by
  unfold neighborSet Gadj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The three given neighbours are *all* the neighbours of a degree-3 vertex. -/
lemma neighborSet_eq_triple (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n) (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u) (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    neighborSet C u = {v₁, v₂, v₃} := by
  obtain ⟨h12, h13, h23⟩ := hdist
  have hsub : ({v₁, v₂, v₃} : Finset (Fin n)) ⊆ neighborSet C u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({v₁, v₂, v₃} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard]; rw [degree] at hu; omega

/-
The matrix quadratic form is bounded above by the simple-graph (`Gadj`,
weight-one) form for nonnegative vectors, since every bond `√(C i j * C j i) ≥ 1`.
-/
lemma form_le_Gadj (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    dotProduct (star x) ((SymmMatrix C).mulVec x) ≤
      2 * (∑ i, (x i) ^ 2) - ∑ i, ∑ j, (if Gadj C i j then x i * x j else 0) := by
  simp only [Matrix.mulVec, dotProduct]
  -- Apply the inequality term by term to the double sum.
  have h_term_by_term : ∀ i j,
      x i * SymmMatrix C i j * x j
      ≤ (if i = j then 2 * x i * x j else 0) - (if Gadj C i j then x i * x j else 0) := by
    intro i j
    split_ifs
    <;> simp_all [SymmMatrix]
    · exact absurd ‹Gadj C j j› (by unfold Gadj; aesop)
    · linarith
    · exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (hx i)
        (by exact_mod_cast SymmMatrix_bond_ge_one C hGCM ‹_› (by unfold Gadj at *; tauto))) (hx j)
    · exact mul_nonneg (mul_nonneg (hx i) (Real.sqrt_nonneg _)) (hx j)
  convert Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_term_by_term i j using 1
  simp only [Finset.mul_sum _ _ _, mul_assoc]
  ring!
  simp [Finset.sum_ite, mul_assoc, sq]
  rw [Finset.mul_sum _ _ _]

/-- The only neighbour of `u` lying in the branch through `v₁` is `v₁` itself. -/
lemma only_neighbor_in_branch (C : Matrix (Fin n) (Fin n) ℤ) (u v₁ v₂ v₃ : Fin n)
    (htrip : neighborSet C u = {v₁, v₂, v₃})
    (hd12 : Disjoint (branchFinset C u v₁) (branchFinset C u v₂))
    (hd13 : Disjoint (branchFinset C u v₁) (branchFinset C u v₃))
    (i : Fin n) (hi : i ∈ branchFinset C u v₁) (hg : Gadj C u i) : i = v₁ := by
  have hmem : i ∈ neighborSet C u := (neighbor_iff_Gadj C u i).mpr hg
  rw [htrip] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hv₂ : v₂ ∈ branchFinset C u v₂ := (mem_branchFinset C u v₂ v₂).mpr Relation.ReflTransGen.refl
  have hv₃ : v₃ ∈ branchFinset C u v₃ := (mem_branchFinset C u v₃ v₃).mpr Relation.ReflTransGen.refl
  rcases hmem with rfl | rfl | rfl
  · rfl
  · exact (Finset.disjoint_left.mp hd12 hi hv₂).elim
  · exact (Finset.disjoint_left.mp hd13 hi hv₃).elim

/-- There are no edges between distinct branches. -/
lemma branch_no_cross_edge (C : Matrix (Fin n) (Fin n) ℤ) (u v v' : Fin n)
    (hvu : v ≠ u) (hv'u : v' ≠ u)
    (hd : Disjoint (branchFinset C u v) (branchFinset C u v'))
    {i j : Fin n} (hi : i ∈ branchFinset C u v) (hj : j ∈ branchFinset C u v') :
    ¬ Gadj C i j := by
  intro hg
  have hiu : i ≠ u := reachExcl_ne_u C u v i ((mem_branchFinset C u v i).mp hi) hvu
  have hju : j ≠ u := reachExcl_ne_u C u v' j ((mem_branchFinset C u v' j).mp hj) hv'u
  have hreach : reachExcl C u v j :=
    ((mem_branchFinset C u v i).mp hi).tail ⟨hg.1, hiu, hju, hg.2⟩
  exact Finset.disjoint_left.mp hd ((mem_branchFinset C u v j).mpr hreach) hj


/-
Sum of squares of the assembled test vector.
-/
lemma assembly_sq (C : Matrix (Fin n) (Fin n) ℤ) (u v₁ v₂ v₃ : Fin n)
    (y₁ y₂ y₃ : Fin n → ℝ)
    (hu1 : u ∉ branchFinset C u v₁) (hu2 : u ∉ branchFinset C u v₂) (hu3 : u ∉ branchFinset C u v₃)
    (hs1 : ∀ i, i ∉ branchFinset C u v₁ → y₁ i = 0)
    (hs2 : ∀ i, i ∉ branchFinset C u v₂ → y₂ i = 0)
    (hs3 : ∀ i, i ∉ branchFinset C u v₃ → y₃ i = 0)
    (hd12 : Disjoint (branchFinset C u v₁) (branchFinset C u v₂))
    (hd13 : Disjoint (branchFinset C u v₁) (branchFinset C u v₃))
    (hd23 : Disjoint (branchFinset C u v₂) (branchFinset C u v₃)) :
    ∑ i, (if i = u then (1 : ℝ) else y₁ i + y₂ i + y₃ i) ^ 2
      = 1 + (∑ i ∈ branchFinset C u v₁, (y₁ i) ^ 2)
          + (∑ i ∈ branchFinset C u v₂, (y₂ i) ^ 2)
          + (∑ i ∈ branchFinset C u v₃, (y₃ i) ^ 2) := by
  have h_split : ∀ i, ((y₁ i + y₂ i + y₃ i) ^ 2 = (y₁ i) ^ 2 + (y₂ i) ^ 2 + (y₃ i) ^ 2) := by
    intro i
    by_cases hi1 : i ∈ branchFinset C u v₁
    <;> by_cases hi2 : i ∈ branchFinset C u v₂
    <;> by_cases hi3 : i ∈ branchFinset C u v₃
    <;> simp_all [Finset.disjoint_left]
  simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']
  rw [Finset.sum_congr rfl fun i hi => h_split i]
  norm_num [Finset.sum_add_distrib, add_assoc]
  rw [← Finset.sum_subset (Finset.subset_univ (branchFinset C u v₁)) fun i hi₁ hi₂ => by aesop,
      ← Finset.sum_subset (Finset.subset_univ (branchFinset C u v₂)) fun i hi₁ hi₂ => by aesop,
      ← Finset.sum_subset (Finset.subset_univ (branchFinset C u v₃)) fun i hi₁ hi₂ => by aesop]
  aesop


/-
Cross (quadratic) term of the assembled test vector.
-/
lemma assembly_cross (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (u v₁ v₂ v₃ : Fin n) (y₁ y₂ y₃ : Fin n → ℝ)
    (htrip : neighborSet C u = {v₁, v₂, v₃})
    (hu1 : u ∉ branchFinset C u v₁) (hu2 : u ∉ branchFinset C u v₂) (hu3 : u ∉ branchFinset C u v₃)
    (hs1 : ∀ i, i ∉ branchFinset C u v₁ → y₁ i = 0)
    (hs2 : ∀ i, i ∉ branchFinset C u v₂ → y₂ i = 0)
    (hs3 : ∀ i, i ∉ branchFinset C u v₃ → y₃ i = 0)
    (hd12 : Disjoint (branchFinset C u v₁) (branchFinset C u v₂))
    (hd13 : Disjoint (branchFinset C u v₁) (branchFinset C u v₃))
    (hd23 : Disjoint (branchFinset C u v₂) (branchFinset C u v₃)) :
    (∑ i, ∑ j, (if Gadj C i j then
        (if i = u then (1 : ℝ) else y₁ i + y₂ i + y₃ i) *
        (if j = u then (1 : ℝ) else y₁ j + y₂ j + y₃ j) else 0))
      = (∑ i ∈ branchFinset C u v₁, ∑ j ∈ branchFinset C u v₁,
            if Gadj C i j then y₁ i * y₁ j else 0)
        + (∑ i ∈ branchFinset C u v₂, ∑ j ∈ branchFinset C u v₂,
            if Gadj C i j then y₂ i * y₂ j else 0)
        + (∑ i ∈ branchFinset C u v₃, ∑ j ∈ branchFinset C u v₃,
            if Gadj C i j then y₃ i * y₃ j else 0)
        + 2 * (y₁ v₁ + y₂ v₂ + y₃ v₃) := by
  have h_split : ∀ i, ∀ j,
      (if Gadj C i j then (y₁ i + y₂ i + y₃ i) * (y₁ j + y₂ j + y₃ j) else 0)
      = (if Gadj C i j then y₁ i * y₁ j else 0) + (if Gadj C i j then y₂ i * y₂ j else 0)
        + (if Gadj C i j then y₃ i * y₃ j else 0) := by
    intros i j
    by_cases h_adj : Gadj C i j
    · by_cases hi1 : i ∈ branchFinset C u v₁
      <;> by_cases hj1 : j ∈ branchFinset C u v₁
      <;> simp_all [Finset.disjoint_left]
      · grind +locals
      · grind +locals
      · grind +locals
    · simp [h_adj]
  calc
    _ = (∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u, (if Gadj C i j then
            (y₁ i + y₂ i + y₃ i) * (y₁ j + y₂ j + y₃ j) else 0))
          + (∑ i ∈ Finset.univ.erase u, if Gadj C u i then (y₁ i + y₂ i + y₃ i) else 0)
          + (∑ j ∈ Finset.univ.erase u, if Gadj C j u then (y₁ j + y₂ j + y₃ j) else 0) := by
      simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', Finset.sum_add_distrib, add_assoc]
      simp [Finset.filter_erase, Gadj_irr]
      ring_nf
      rw [show (∑ x : Fin n, ↑ (if Gadj C x u then {u} else ∅ : Finset (Fin n)).card * y₁ x)
        = ∑ x ∈ Finset.filter (fun x => Gadj C x u) Finset.univ, y₁ x from ?_,
        show (∑ x : Fin n, ↑ (if Gadj C x u then {u} else ∅ : Finset (Fin n)).card * y₂ x)
        = ∑ x ∈ Finset.filter (fun x => Gadj C x u) Finset.univ, y₂ x from ?_,
        show (∑ x : Fin n, ↑ (if Gadj C x u then {u} else ∅ : Finset (Fin n)).card * y₃ x)
        = ∑ x ∈ Finset.filter (fun x => Gadj C x u) Finset.univ, y₃ x from ?_]
      ring!
      · rw [Finset.sum_filter] ; congr ; ext ; aesop
      · rw [Finset.sum_filter] ; congr ; ext ; aesop
      · rw [Finset.sum_filter] ; congr ; ext ; aesop
    _ = (∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u,
          (if Gadj C i j then y₁ i * y₁ j else 0)
        + ∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u,
          (if Gadj C i j then y₂ i * y₂ j else 0)
        + ∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u,
          (if Gadj C i j then y₃ i * y₃ j else 0))
        + 2 * (∑ i ∈ Finset.univ.erase u, if Gadj C u i then (y₁ i + y₂ i + y₃ i) else 0) := by
      rw [add_assoc]
      congr! 1
      · simp only [← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => h_split i j]
      · grind +suggestions
    _ = (∑ i ∈ branchFinset C u v₁, ∑ j ∈ branchFinset C u v₁,
            if Gadj C i j then y₁ i * y₁ j else 0)
        + (∑ i ∈ branchFinset C u v₂, ∑ j ∈ branchFinset C u v₂,
            if Gadj C i j then y₂ i * y₂ j else 0)
        + (∑ i ∈ branchFinset C u v₃, ∑ j ∈ branchFinset C u v₃,
            if Gadj C i j then y₃ i * y₃ j else 0)
        + 2 * (y₁ v₁ + y₂ v₂ + y₃ v₃) := by
      congr 1
      · congr 1
        congr 1
        · have : branchFinset C u v₁ ⊆ Finset.univ.erase u := by
            intro x hx
            apply Finset.mem_erase_of_ne_of_mem
            · rintro rfl
              exact hu1 hx
            · apply Finset.mem_univ
          rw [← Finset.sum_subset this]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_subset this]
            grind
          · simp +contextual [hs1]
        · have : branchFinset C u v₂ ⊆ Finset.univ.erase u := by
            intro x hx
            apply Finset.mem_erase_of_ne_of_mem
            · rintro rfl
              exact hu2 hx
            · apply Finset.mem_univ
          rw [← Finset.sum_subset this]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_subset this]
            grind
          · simp +contextual [hs2]
        · have : branchFinset C u v₃ ⊆ Finset.univ.erase u := by
            intro x hx
            apply Finset.mem_erase_of_ne_of_mem
            · rintro rfl
              exact hu3 hx
            · apply Finset.mem_univ
          rw [← Finset.sum_subset this]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_subset this]
            grind
          · simp +contextual [hs3]
      · congr 1
        have : {v₁, v₂, v₃} ⊆ Finset.univ.erase u := by grind +suggestions
        rw [← Finset.sum_subset this]
        · have hv1 := branchFinset_refl C u v₁
          have hv2 := branchFinset_refl C u v₂
          have hv3 := branchFinset_refl C u v₃
          have hv12 := Finset.disjoint_left.mp hd12 hv1
          have hv13 := Finset.disjoint_left.mp hd13 hv1
          have hv21 := Finset.disjoint_right.mp hd12 hv2
          have hv23 := Finset.disjoint_left.mp hd23 hv2
          have hv31 := Finset.disjoint_right.mp hd13 hv3
          have hv32 := Finset.disjoint_right.mp hd23 hv3
          have h_distinct : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
            split_ands
            <;> rintro rfl
            <;> contradiction
          simp [*, Finset.sum_singleton]
          simp [← neighbor_iff_Gadj, htrip]
          ring_nf
        · simp +contextual [← htrip, neighbor_iff_Gadj]

/-- If there is a path from `v` to `v'` avoiding `u` (`reachExcl C u v v'`), while
`u` is adjacent to both `v` and `v'` and `v ≠ v'`, then closing the path through `u`
yields a genuine cycle, contradicting positive-definiteness via `no_cycle`. -/
lemma no_posDef_of_branch_path (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (u v v' : Fin n) (hvv : v ≠ v')
    (hv : Gadj C u v) (hv' : Gadj C u v') (hpath : reachExcl C u v v') :
    ¬(SymmMatrix C).PosDef := by
  -- If $u$ and $v$ are adjacent, then by `reachExcl_ne_u`, $v \ne u$.
  have hv_ne_u : v ≠ u := by
    exact hv.1.symm
  have hv'_ne_u : v' ≠ u := by
    exact hv'.1.symm
  obtain ⟨s, hs⟩ : ∃ s : List (Fin n),
      s.head? = some v ∧
      s.getLast? = some v' ∧
      s.Nodup ∧
      List.IsChain (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u) s := by
    obtain ⟨p, hp⟩ : ∃ p : SimpleGraph.Walk
        (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v', p.IsPath := by
      obtain ⟨p, hp⟩ : ∃ p : SimpleGraph.Walk
          (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v', True := by
        have h_reachable : SimpleGraph.Reachable
            (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v' := by
          have h_path : ∀ {i j : Fin n}, reachExcl C u i j → SimpleGraph.Reachable
              (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) i j := by
            intro i j hij
            induction hij
            · aesop
            · rename_i k hk₁ hk₂ hk₃
              exact hk₃.trans (SimpleGraph.Adj.reachable <| by
                unfold adjExcl at hk₂; unfold Gadj; aesop)
          exact h_path hpath
        exact ⟨h_reachable.some, trivial⟩;
      exact ⟨p.toPath, p.toPath.isPath⟩;
    refine' ⟨p.support, _, _, _, _⟩
    <;> simp_all +decide [SimpleGraph.Walk.isPath_def];
    · cases p <;> aesop;
    · cases p <;> simp_all +decide [List.getLast?];
    · simp_all +decide [List.isChain_iff_getElem];
      intro i hi
      have := p.adj_getVert_succ hi
      simp_all +decide [SimpleGraph.fromRel_adj];
      grind +suggestions;
  -- Put `L := u :: s`. Then `L.length = s.length + 1 ≥ 3`,
  -- and `L.Nodup` by `List.nodup_cons.mpr ⟨hnotu, hs.2.2.1⟩`.
  set L : List (Fin n) := u :: s
  have hL_len : 3 ≤ L.length := by
    rcases s with (_ | ⟨x, _ | ⟨y, s⟩⟩)
    <;> simp_all +decide; all_goals grind
  have hL_nodup : L.Nodup := by
    simp +zetaDelta at *
    have := hs.2.2.2; simp_all +decide [List.isChain_iff_getElem]
    intro hu
    rcases List.mem_iff_get.mp hu with ⟨i, hi⟩
    rcases i with ⟨_ | i, hi⟩
    <;> simp_all +decide
    cases s <;> aesop
  have hL_cycle : ∀ i : Fin L.length,
      C (L.get i) (L.get ⟨(i.val + 1) % L.length, Nat.mod_lt _ (by omega)⟩) ≠ 0 := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = L.length - 1
    · rcases hi with (hi | hi)
      <;> simp_all +decide;
      · rcases s with (_ | ⟨x, _ | ⟨y, s⟩⟩)
        <;> simp_all +decide [Gadj]
        · grind;
        · aesop;
      · simp +zetaDelta at *;
        convert hv'.2 using 1;
        grind +splitIndPred;
    · have := List.isChain_iff_getElem.mp hs.2.2.2
      rcases i with ⟨_ | i, hi⟩ <;> simp_all +decide
      have := this i (by grind)
      generalize_proofs at *;
      simp +zetaDelta at *;
      simp_all +decide [Nat.mod_eq_of_lt (by linarith : i + 1 + 1 < s.length + 1), Gadj];
  have hemb : Function.Injective L.get := List.nodup_iff_injective_get.mp hL_nodup
  exact no_cycle C hGCM L.length hL_len ⟨L.get, hemb⟩ hL_cycle

/-- **Distinctness of branches.**  At a degree-3 vertex of a positive-definite
Dynkin graph, the three branches are pairwise disjoint (otherwise there is a cycle
through `u`, contradicting acyclicity of positive-definite Dynkin diagrams). -/
lemma branches_disjoint (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (hP : (SymmMatrix C).PosDef) (u : Fin n) (v v' : Fin n) (hvv : v ≠ v')
    (hv : v ∈ neighborSet C u) (hv' : v' ∈ neighborSet C u) :
    Disjoint (branchFinset C u v) (branchFinset C u v') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  have hadjsymm : Symmetric (adjExcl C u) := by
    rintro a b ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3, h2, fun h => h4 ((hGCM.vanish_symm b a).mp h)⟩
  have hreach_w : reachExcl C u v w := (mem_branchFinset C u v w).mp hw
  have hreach_w' : reachExcl C u v' w := (mem_branchFinset C u v' w).mp hw'
  have hpath : reachExcl C u v v' :=
    hreach_w.trans (Relation.ReflTransGen.symmetric hadjsymm hreach_w')
  exact no_posDef_of_branch_path C hGCM u v v' hvv
    ((neighbor_iff_Gadj C u v).mp hv) ((neighbor_iff_Gadj C u v').mp hv') hpath hP

/-- The analytic core (Schur complement positivity): for a degree-3 vertex of a
positive-definite Dynkin graph, the sum of `aᵢ/(aᵢ+1)` over the three branches is
strictly below `2`. -/
lemma schur_ineq (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    (branchSize C u v₁ : ℝ) / ((branchSize C u v₁ : ℝ) + 1) +
    (branchSize C u v₂ : ℝ) / ((branchSize C u v₂ : ℝ) + 1) +
    (branchSize C u v₃ : ℝ) / ((branchSize C u v₃ : ℝ) + 1) < 2 := by
  by_contra hcon
  push_neg at hcon
  have htrip := neighborSet_eq_triple C u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist
  have hv₁u : v₁ ≠ u := ((neighbor_iff_Gadj C u v₁).mp hv₁).1.symm
  have hv₂u : v₂ ≠ u := ((neighbor_iff_Gadj C u v₂).mp hv₂).1.symm
  have hv₃u : v₃ ≠ u := ((neighbor_iff_Gadj C u v₃).mp hv₃).1.symm
  have hu1 := u_notMem_branch C u v₁ hv₁u
  have hu2 := u_notMem_branch C u v₂ hv₂u
  have hu3 := u_notMem_branch C u v₃ hv₃u
  have hd12 := branches_disjoint C hGCM hP u v₁ v₂ hdist.1 hv₁ hv₂
  have hd13 := branches_disjoint C hGCM hP u v₁ v₃ hdist.2.1 hv₁ hv₃
  have hd23 := branches_disjoint C hGCM hP u v₂ v₃ hdist.2.2 hv₂ hv₃
  obtain ⟨y₁, hy₁nn, hy₁s, hy₁E⟩ := branch_marking C hGCM u v₁
  obtain ⟨y₂, hy₂nn, hy₂s, hy₂E⟩ := branch_marking C hGCM u v₂
  obtain ⟨y₃, hy₃nn, hy₃s, hy₃E⟩ := branch_marking C hGCM u v₃
  have hxne : (fun i => if i = u then (1 : ℝ) else y₁ i + y₂ i + y₃ i) ≠ 0 := by
    intro h
    have : (fun i => if i = u then (1 : ℝ) else y₁ i + y₂ i + y₃ i) u = 0 := by
      rw [h]
      rfl
    simp at this
  have hpos := hP.dotProduct_mulVec_pos hxne
  have hxnn : ∀ i, 0 ≤ (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) i := by
    intro i
    simp only
    split_ifs
    · norm_num
    · exact add_nonneg (add_nonneg (hy₁nn i) (hy₂nn i)) (hy₃nn i)
  have hle := form_le_Gadj C hGCM (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) hxnn
  have hsq := assembly_sq C u v₁ v₂ v₃ y₁ y₂ y₃ hu1 hu2 hu3 hy₁s hy₂s hy₃s hd12 hd13 hd23
  have hcr := assembly_cross C hGCM u v₁ v₂ v₃ y₁ y₂ y₃ htrip hu1 hu2 hu3 hy₁s hy₂s hy₃s
    hd12 hd13 hd23
  rw [hsq, hcr] at hle
  linarith [hpos, hle, hy₁E, hy₂E, hy₃E, hcon]

theorem branchSize_inequality (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    (1 : ℝ) / ((branchSize C u v₁ : ℝ) + 1) +
    (1 : ℝ) / ((branchSize C u v₂ : ℝ) + 1) +
    (1 : ℝ) / ((branchSize C u v₃ : ℝ) + 1) > 1 := by
  have key := schur_ineq C hGCM hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist
  set a : ℝ := (branchSize C u v₁ : ℝ) with ha
  set b : ℝ := (branchSize C u v₂ : ℝ) with hb
  set c : ℝ := (branchSize C u v₃ : ℝ) with hc
  have ha1 : (a:ℝ) + 1 ≠ 0 := by positivity
  have hb1 : (b:ℝ) + 1 ≠ 0 := by positivity
  have hc1 : (c:ℝ) + 1 ≠ 0 := by positivity
  have e₁ : a / (a + 1) = 1 - 1 / (a + 1) := by field_simp; ring
  have e₂ : b / (b + 1) = 1 - 1 / (b + 1) := by field_simp; ring
  have e₃ : c / (c + 1) = 1 - 1 / (c + 1) := by field_simp; ring
  rw [e₁, e₂, e₃] at key
  linarith

lemma reciprocal_sum_gt_one_bounds (a b c : ℕ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (h : 1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) + 1 / ((c : ℝ) + 1) > 1) :
    a = 1 ∧ (b = 1 ∨ b = 2 ∧ c ≤ 4) := by
  have hab' : 1 / ((a : ℝ) + 1) ≥ 1 / ((b : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num [hab]
  have hbc' : 1 / ((b : ℝ) + 1) ≥ 1 / ((c : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num [hbc]
  have ha1 : a = 1 := by
    by_contra
    have ha1d3 : 1 / ((a : ℝ) + 1) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le
      · positivity
      · norm_num [← tsub_le_iff_right]
        omega
    have hb1d3 : 1 / ((b : ℝ) + 1) ≤ 1 / 3 := by linarith
    have hc1d3 : 1 / ((c : ℝ) + 1) ≤ 1 / 3 := by linarith
    linarith
  subst a
  simp
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  · by_cases hb2 : b = 2
    · subst b
      simp
      by_contra
      have hc1d5 : 1 / ((c : ℝ) + 1) ≤ 1 / 6 := by
        apply one_div_le_one_div_of_le
        · positivity
        · norm_num [← tsub_le_iff_right]
          omega
      linarith
    · have hb1d4 : 1 / ((b : ℝ) + 1) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le
        · positivity
        · norm_num [← tsub_le_iff_right]
          omega
      have hc1d4 : 1 / ((c : ℝ) + 1) ≤ 1 / 4 := by linarith
      linarith

theorem branchSize_bounds (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (h12 : branchSize C u v₁ ≤ branchSize C u v₂)
    (h23 : branchSize C u v₂ ≤ branchSize C u v₃) :
      branchSize C u v₁ = 1 ∧
      (branchSize C u v₂ = 1 ∨ branchSize C u v₂ = 2 ∧ branchSize C u v₃ ≤ 4) := by
  have hrecip := branchSize_inequality C hGCM hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist
  have h1 : 0 < branchSize C u v₁ := by
    rw [branchSize_eq_card, Finset.card_pos]
    use v₁
    apply branchFinset_refl
  exact reciprocal_sum_gt_one_bounds (branchSize C u v₁) (branchSize C u v₂) (branchSize C u v₃)
    h1 h12 h23 hrecip
