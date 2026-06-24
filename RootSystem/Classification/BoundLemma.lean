import RootSystem.Classification.DynkinGraph

variable {n : ℕ}

/-
For a GCM and nonneg vector `x`, the quadratic form `xᵀ (SymmMatrix C) x`
    is bounded above by `∑ i, 2 * (x i)^2 - 2 * ∑ edges, x i * x j`
    (since √(Cᵢⱼ·Cⱼᵢ) ≥ 1 for each edge and all off-diagonal contributions are ≤ 0).
-/
lemma symmMatrix_quadform_upper_bound (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx_nn : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n))
    (hE_adj : ∀ p ∈ E, p.2 ∈ neighborSet C p.1)
    (hE_nodup : ∀ p ∈ E, (p.2, p.1) ∉ E) :
    dotProduct x ((SymmMatrix C).mulVec x) ≤
      ∑ i : Fin n, 2 * (x i) ^ 2 - 2 * ∑ p ∈ E, x p.1 * x p.2 := by
  -- Expand the quadratic form using the definition of `SymmMatrix`.
  calc
    _ = ∑ i, 2 * (x i) ^ 2 - ∑ i, ∑ j ∈ Finset.univ.erase i, √((C i j) * (C j i)) * x i * x j := by
      simp [SymmMatrix, Matrix.mulVec, dotProduct, Finset.sum_ite, Finset.filter_ne]
      simp [mul_assoc, mul_comm, mul_left_comm, sq]
      ring_nf
      simp [Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, sq, hGCM.diag]
      ring_nf
      simp [Finset.sum_filter, sq]
    _ = ∑ i, 2 * (x i) ^ 2
        - ∑ p : ((Fin n) × (Fin n)) with p.1 ≠ p.2, √((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 := by
      congr 1
      rw [Finset.sum_sigma']
      apply (Finset.sum_bij ( fun p hp => ⟨ p.1, p.2 ⟩ ) _ _ _ _).symm
      <;> simp
      · exact fun a b hab => Ne.symm hab
      · tauto
      · exact fun p hp => ⟨ p.1, p.2, Ne.symm hp, rfl ⟩
    _ ≤ ∑ i, 2 * (x i) ^ 2
        - ∑ p ∈ E.biUnion fun p ↦ {(p.1, p.2), (p.2, p.1)},
            √(↑(C p.1 p.2) * ↑(C p.2 p.1)) * x p.1 * x p.2 := by
      rw [sub_le_sub_iff_left]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      <;> simp [Finset.subset_iff]
      · grind +ring
      · exact fun _ _ _ _ => mul_nonneg ( mul_nonneg ( Real.sqrt_nonneg _ ) ( hx_nn _ ) ) ( hx_nn _ )
    _ = ∑ i, 2 * (x i) ^ 2
        - (∑ p ∈ E, √((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 + ∑ p ∈ E,
            √((C p.2 p.1) * (C p.1 p.2)) * x p.2 * x p.1) := by
      congr 1
      rw [Finset.sum_biUnion]
      · rw [← Finset.sum_add_distrib]
        refine' Finset.sum_congr rfl fun p hp => _ ;
        rw [Finset.sum_pair]
        simp
        grind
      · intro p hp q hq hpq
        simp_all [Finset.disjoint_left]
        grind +splitImp
    _ ≤ ∑ i : Fin n, 2 * (x i) ^ 2 - 2 * ∑ p ∈ E, x p.1 * x p.2 := by
      rw [sub_le_sub_iff_left]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      ring_nf
      have : 1 ≤ √(↑(C p.1 p.2) * ↑(C p.2 p.1)) := by
        simp [neighborSet] at hE_adj
        exact Real.le_sqrt_of_sq_le (
          mod_cast edge_product_ge_one C hGCM p.1 p.2 (hE_adj p.1 p.2 hp |>.2) (hE_adj p.1 p.2 hp |>.1)
        )
      have : 0 ≤ x p.1 * x p.2 := by
        apply mul_nonneg
        <;> apply hx_nn
      nlinarith

/-- Per-vertex bound: if for every vertex i with x i > 0, the sum of x-values
    of its neighbors (in the GCM sense) is ≥ 2 * x i, then the quadratic form
    `xᵀ (SymmMatrix C) x ≤ 0`. -/
lemma quadform_nonpos_of_neighbor_bound (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx_nn : ∀ i, 0 ≤ x i)
    (h_bound : ∀ i, 0 < x i → 2 * x i ≤ ∑ j with j ∈ neighborSet C i, x j) :
    dotProduct x ((SymmMatrix C).mulVec x) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : 0 < x i
  · calc
      _ = 2 * (x i) ^ 2 - x i * ∑ j with i ≠ j, √(C i j * C j i) * x j := by
        simp [SymmMatrix, Matrix.mulVec, dotProduct, Finset.sum_ite]
        simp [Finset.filter_eq, Finset.filter_ne, hGCM.diag]
        ring
      _ ≤ 2 * (x i) ^ 2 - x i * ∑ j with j ∈ neighborSet C i, √(C i j * C j i) * x j := by
        rw [sub_le_sub_iff_left, mul_le_mul_iff_of_pos_left hi]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · simp only [neighborSet]
          intro j hj
          aesop
        · intro j hj hnj
          apply mul_nonneg (Real.sqrt_nonneg _) (hx_nn _)
      _ ≤ 2 * (x i) ^ 2 - x i * ∑ j with j ∈ neighborSet C i, x j := by
        rw [sub_le_sub_iff_left, mul_le_mul_iff_of_pos_left hi]
        apply Finset.sum_le_sum
        intro j jn
        simp [neighborSet] at jn
        apply le_mul_of_one_le_left (hx_nn j)
        rw [Real.one_le_sqrt]
        exact (mod_cast edge_product_ge_one C hGCM i j (by aesop) (by aesop))
      _ ≤ 2 * (x i) ^ 2 - x i * (2 * x i) := by
        rw [sub_le_sub_iff_left, mul_le_mul_iff_of_pos_left hi]
        apply h_bound i hi
      _ = 0 := by
        ring
  · have hi : 0 = x i := by
      apply eq_of_le_of_not_lt (hx_nn i) hi
    simp [← hi]
