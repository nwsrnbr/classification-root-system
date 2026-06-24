import RootSystem.Classification.BoundLemma

variable {n : ℕ}

/-
In a generalized Cartan matrix with positive definite symmetrization,
every vertex has degree at most 3.
-/
theorem pos_degree_le_three (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (hP : (SymmMatrix C).PosDef) (i : Fin n) :
    degree C i ≤ 3 := by
  simp only [degree]
  by_contra h_deg_ge_4
  -- Construct the vector x : Fin n → ℝ with x i = 2 and x j = 1 for j ∈ N, and x j = 0 otherwise.
  set x : Fin n → ℝ := fun j => if j = i then 2 else if j ∈ neighborSet C i then 1 else 0
  -- Define E = {(i, a) | a ∈ N}.
  let E : Finset (Fin n × Fin n) := (neighborSet C i).image (fun a => (i, a))
  -- To apply `symmMatrix_quadform_upper_bound`, prove all required hypotheses.
  have hx_nn : ∀ i, (0 : ℝ) ≤ x i := by intro i; simp only [x]; split_ifs <;> norm_num
  have hE_adj : ∀ p ∈ E, p.2 ∈ neighborSet C p.1 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    simp_all [neighborSet]
  have hE_nodup : ∀ p ∈ E, (p.2, p.1) ∉ E := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    intro hrev
    rcases Finset.mem_image.mp hrev with ⟨b, hb, hb_eq⟩
    have : i = a := by
      simpa using congrArg Prod.fst hb_eq
    simp_all [neighborSet]
  -- Having verified all the required hypotheses, we can apply `symmMatrix_quadform_upper_bound`.
  have h_x_transpose_SymmMatrix_x : x ⬝ᵥ (SymmMatrix C).mulVec x ≤ 0 := by
    calc
      _ ≤ ∑ i, 2 * x i ^ 2 - 2 * ∑ p ∈ E, x p.1 * x p.2 :=
        symmMatrix_quadform_upper_bound C hGCM x hx_nn E hE_adj hE_nodup
      _ = ∑ i, 2 * x i ^ 2 - 2 * (2 * (neighborSet C i).card) := by
        congr
        simp [E]
        rw [Finset.sum_eq_card_nsmul (b := 2)]
        · ring
        · intro a ha
          have : i ≠ a := by
            simp [neighborSet] at ha
            apply ha.2
          simp [x]
          split_ifs
          <;> simp_all
      _ = 8 + (neighborSet C i).card * 2 - 2 * (2 * (neighborSet C i).card) := by
        congr
        simp [x]
        simp [Finset.sum_ite]
        congr
        · norm_num
          simp [Finset.filter_eq']
        · simp [neighborSet]
          grind
      _ = 2 * 4 - 2 * (neighborSet C i).card := by
        ring
      _ ≤ 0 := by
        simp
        omega
  -- Since $x$ is nonzero, we have $x^T (SymmMatrix C) x > 0$.
  have hx_ne : x ≠ 0 := by
    intro h
    have : x i = 2 := by simp [x]
    have : x i = 0 := by simp [h]
    linarith
  have h_pos := hP.dotProduct_mulVec_pos hx_ne
  simp [star] at h_pos
  linarith
