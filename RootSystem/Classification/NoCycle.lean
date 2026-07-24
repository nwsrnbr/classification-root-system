import RootSystem.Classification.BoundLemma

variable {n : ℕ}

/-
A cycle of length ≥ 3 in a GCM with positive definite symmetrization is impossible.
    Here the cycle is given as an injective map `f : Fin k → Fin n` with `f i` adjacent to
    `f (i+1 mod k)` for all `i`.
-/
theorem no_cycle (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (k : ℕ) (hk : 3 ≤ k) (f : Fin k ↪ Fin n)
    (hcycle : ∀ i : Fin k, C (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0) :
    ¬(SymmMatrix C).PosDef := by
  -- Define the vector x such that x_i = 1 for all i in the cycle, and x_i = 0 elsewhere.
  let x : Fin n → ℝ := fun i => if ∃ j : Fin k, i = f j then 1 else 0
  have hx_ne : x ≠ 0 := by
    intro h
    have hx_at : x (f ⟨0, by omega⟩) = 1 := by simp [x]
    simp [h] at hx_at
  have hx_nn : ∀ i, (0 : ℝ) ≤ x i := by intro i; simp only [x]; split_ifs <;> norm_num
  have h_neighbor_bound : ∀ i, 0 < x i → 2 * x i ≤ ∑ j with j ∈ neighborSet C i, x j := by
    intro i hxi
    obtain ⟨r, hi_mem⟩ : ∃ r : Fin k, i = f r := by
      simp [x] at hxi
      split_ifs at hxi with hxi'
      <;> simp_all
    simp [hi_mem, x]
    let r₁ : Fin k := ⟨(r.val + 1) % k, Nat.mod_lt _ (by omega)⟩
    let r₂ : Fin k := ⟨(r.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
    have hr1_ne : r ≠ r₁ := by
      simp [Fin.ext_iff, r₁]
      rw [Nat.mod_eq]
      split_ifs
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · omega
    have hr2_ne : r ≠ r₂ := by
      simp [Fin.ext_iff, r₂]
      rw [Nat.mod_eq]
      split_ifs
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · omega
    have hr12_ne : r₁ ≠ r₂ := by
      simp [r₁, r₂]
      rw [Nat.mod_eq]
      nth_rw 2 [Nat.mod_eq]
      split_ifs
      <;> simp_all
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · omega
    rw [Finset.le_card_iff_exists_subset_card]
    use {f r₁, f r₂}
    split_ands
    · simp [Finset.subset_iff]
      split_ands
      · simp [neighborSet]
        exact ⟨hcycle r, hr1_ne⟩
      · simp [neighborSet]
        split_ands
        · rw [hGCM.vanish_symm]
          have : (r₂ + 1) % k = r := by
            simp [r₂]
            rw [Nat.mod_eq]
            split_ifs
            · rw [Nat.mod_eq_of_lt (by omega)]
              omega
            · omega
          simpa [this] using hcycle r₂
        · apply hr2_ne
    · simp [hr12_ne]
  have h_le := quadform_nonpos_of_neighbor_bound C hGCM x hx_nn h_neighbor_bound
  -- This contradicts positive definiteness
  intro hPD
  have h_pos := hPD.dotProduct_mulVec_pos hx_ne
  simp [star] at h_pos
  linarith
