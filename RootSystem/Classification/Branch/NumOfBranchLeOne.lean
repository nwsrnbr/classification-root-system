import RootSystem.Classification.BoundLemma

variable {n : ℕ}

/-
If vertex `i` has degree ≥ 3 and `w` is one specific neighbor, there exist
    two more distinct neighbors `a`, `b` of `i` with `a ≠ w` and `b ≠ w`.
-/
lemma exist_two_extra_neighbors (C : Matrix (Fin n) (Fin n) ℤ)
    (i w : Fin n) (hdeg : 3 ≤ degree C i) :
    ∃ a b : Fin n, a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ a ∈ neighborSet C i ∧ b ∈ neighborSet C i := by
  have h_card : ∃ S : Finset (Fin n), S.card ≥ 2 ∧ ∀ j ∈ S, j ≠ w ∧ j ∈ neighborSet C i := by
    use neighborSet C i \ {w}
    simp_all only [Finset.card_sdiff, degree, neighborSet]
    split_ands
    · apply Nat.le_sub_of_add_le
      apply le_trans' hdeg
      apply add_le_of_le_tsub_left_of_le (by norm_num)
      rw [Finset.card_le_one]
      simp
    · aesop
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_card
  obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hS₁
  use a, b
  aesop

/-- For a GCM with positive-definite symmetrization, if there exist two branch
    vertices u ≠ v (each of degree ≥ 3), then there is a nonzero nonneg vector
    `x` with `xᵀ (SymmMatrix C) x ≤ 0`, contradicting positive definiteness.
    The vector assigns 2 to each vertex on a path from u to v,
    and 1 to the extra neighbors of u and v. -/
lemma not_posDef_of_two_branches (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C)
    (u v : Fin n) (huv : u ≠ v)
    (hu_branch : 3 ≤ degree C u) (hv_branch : 3 ≤ degree C v) :
    ¬(SymmMatrix C).PosDef := by
  -- Step 1: Get a path from u to v
  have hr : (dynkinGraph C hGCM).Reachable u v := dynkinGraph_preconnected C hGCM hI u v
  obtain ⟨walk⟩ := hr
  let path := walk.toPath
  have hpath_isPath : path.val.IsPath := path.property
  -- The path has length ≥ 1 since u ≠ v
  have hlen : 1 ≤ path.val.length := by
    by_contra h
    push Not at h
    have h0 : path.val.length = 0 := Nat.lt_one_iff.mp h
    exact huv (SimpleGraph.Walk.Nil.eq (SimpleGraph.Walk.nil_iff_length_eq.mpr h0))
  -- Step 2: Get the second vertex of the path and extra neighbors of u
  let w₁ := path.val.getVert 1
  have hadj_u_w1 : (dynkinGraph C hGCM).Adj u w₁ := by
    have := path.val.adj_getVert_succ (by omega : 0 < path.val.length)
    rwa [path.val.getVert_zero] at this
  obtain ⟨a₁, a₂, ha_ne, ha1_ne_w1, ha2_ne_w1, hCa1, hCa2⟩ :=
    exist_two_extra_neighbors C u w₁ hu_branch
  -- Step 3: Get the second-to-last vertex and extra neighbors of v
  let w₂ := path.val.getVert (path.val.length - 1)
  have hadj_w2_v : (dynkinGraph C hGCM).Adj w₂ v := by
    have h := path.val.adj_getVert_succ (show path.val.length - 1 < path.val.length by omega)
    rw [Nat.sub_one_add_one_eq_of_pos (by omega), path.val.getVert_length] at h; exact h
  obtain ⟨b₁, b₂, hb_ne, hb1_ne_w2, hb2_ne_w2, hCb1, hCb2⟩ :=
    exist_two_extra_neighbors C v w₂ hv_branch
  -- Step 4: Construct the vector x
  let pathVerts : Finset (Fin n) := path.val.support.toFinset
  let x : Fin n → ℝ := fun i =>
    if i ∈ pathVerts then 2
    else if i = a₁ ∨ i = a₂ ∨ i = b₁ ∨ i = b₂ then 1
    else 0
  -- Step 5: x ≠ 0 and x ≥ 0
  have hx_ne : x ≠ 0 := by
    intro h
    have hu_in : u ∈ pathVerts := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support path.val)
    have : x u = 0 := congr_fun h u
    simp only [x, hu_in, ite_true] at this; norm_num at this
  have hx_nn : ∀ i, (0 : ℝ) ≤ x i := by intro i; simp only [x]; split_ifs <;> norm_num
  -- Step 6: Apply the per-vertex bound
  -- For each vertex i with x i > 0, show 2 * x i ≤ ∑ neighbors x j.
  -- Case analysis: i is on the path, or i is an extra neighbor.
  have h_neighbor_bound : ∀ i, 0 < x i → 2 * x i ≤ ∑ j with j ∈ neighborSet C i, x j := by
    intro i hxi
    -- x i > 0 means i is on the path (x i = 2) or i is an extra (x i = 1)
    simp only [x] at hxi ⊢
    simp_all only [neighborSet]
    split_ifs at hxi with h_path h_extra
    · -- i is on the path: x i = 2, need ∑ neighbors ≥ 4
      by_cases hi : i = u ∨ i = v
      · rcases hi with ( rfl | rfl )
        <;> simp_all
        · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ )
          any_goals exact { w₁, a₁, a₂ }
          · rw [Finset.sum_insert, Finset.sum_insert]
            <;> simp +decide [ * ]
            · split_ifs
              <;> norm_num
              · simp +zetaDelta at *
              · simp +zetaDelta at *
              · simp +zetaDelta at *
              · simp +zetaDelta at *
            · exact ⟨ Ne.symm ha1_ne_w1, Ne.symm ha2_ne_w1 ⟩
          · simp_all +decide [ Finset.subset_iff, dynkinGraph ]
          · exact fun _ _ _ => hx_nn _
        · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ )
          any_goals exact { w₂, b₁, b₂ }
          · rw [Finset.sum_insert, Finset.sum_insert]
            <;> simp +decide [ * ]
            · split_ifs
              <;> norm_num
              · simp +zetaDelta at *
              · simp +zetaDelta at *
              · simp +zetaDelta at *
              · simp +zetaDelta at *
            · exact ⟨Ne.symm hb1_ne_w2, Ne.symm hb2_ne_w2⟩
          · simp_all +decide [Finset.subset_iff, dynkinGraph]
            grind
          · exact fun _ _ _ => hx_nn _
      · -- Since $i$ is not $u$ or $v$, it must be an interior vertex of the path.
        obtain ⟨k, hk₁, hk₂, hk₃⟩ : ∃ k : ℕ, 0 < k ∧ k < path.val.length ∧ path.val.getVert k = i := by
          simp +zetaDelta at *
          rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h_path
          obtain ⟨ k, hk₁, hk₂ ⟩ := h_path
          use k
          split_ands
          · rcases k with (_ | k)
            <;> simp_all
          · apply lt_of_le_of_ne hk₂
            rintro rfl
            simp_all
          · apply hk₁
        -- Since $i$ is an interior vertex, it has at least two neighbors on the path.
        have h_neighbors : (path.val.getVert (k - 1)) ∈ pathVerts ∧
            (path.val.getVert (k + 1)) ∈ pathVerts ∧
            (path.val.getVert (k - 1)) ≠ i ∧
            (path.val.getVert (k + 1)) ≠ i ∧
            C i (path.val.getVert (k - 1)) ≠ 0 ∧
            C i (path.val.getVert (k + 1)) ≠ 0 := by
          simp +zetaDelta
          rw [← hk₃]
          have hk₄ : (dynkinGraph C hGCM).Adj (path.val.getVert k) (path.val.getVert (k - 1)) := by
            have hk : k = k - 1 + 1 := by omega
            nth_rw 1 [hk]
            apply SimpleGraph.Adj.symm
            apply SimpleGraph.Walk.adj_getVert_succ
            omega
          have hk₅ : (dynkinGraph C hGCM).Adj (path.val.getVert k) (path.val.getVert (k + 1)) := by
            apply SimpleGraph.Walk.adj_getVert_succ
            omega
          exact ⟨hk₄.symm.2, hk₅.symm.2, hk₄.1, hk₅.1⟩
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        any_goals exact { ( path.val.getVert ( k - 1 ) ), ( path.val.getVert ( k + 1 ) ) };
        · rw [ Finset.sum_pair ]
          <;> norm_num [ h_neighbors ]
          · split_ifs
            norm_num
          · intro h
            have := hpath_isPath.getVert_injOn
            simp only [Set.InjOn] at this
            have : k - 1 = k + 1 := by
              apply this
              <;> grind
            simp at this
        · grind
        · exact fun _ _ _ => hx_nn _
    · -- i is an extra neighbor: x i = 1, need ∑ neighbors ≥ 2
      rcases h_extra with ( rfl | rfl | rfl | rfl );
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show u ∈ _ from _ ) )
        <;> simp_all +decide [ dynkinGraph ];
        · simp +zetaDelta at *;
        · split_ifs <;> norm_num;
        · grind +revert;
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show u ∈ _ from _ ) )
        <;> simp_all +decide [ dynkinGraph ];
        · exact if_pos ( by exact List.mem_toFinset.mpr <| by simp ) |> fun h => h.symm ▸ by norm_num;
        · split_ifs <;> norm_num;
        · simpa [hGCM.vanish_symm, eq_comm]
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => by positivity ) ( show v ∈ _ from _ ) )
        <;> simp +decide [ * ];
        · simp +zetaDelta at *;
        · simpa [hGCM.vanish_symm, eq_comm] using hCb1
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show v ∈ _ from _ ) )
        <;> simp_all +decide [ dynkinGraph ];
        · -- Since $v$ is in the pathVerts, the if statement evaluates to 2.
          simp [pathVerts];
        · split_ifs <;> norm_num;
        · simpa [hGCM.vanish_symm, eq_comm]
    · -- x i = 0, contradiction
      linarith
  -- Step 7: Apply quadform_nonpos_of_neighbor_bound
  have h_le := quadform_nonpos_of_neighbor_bound C hGCM x hx_nn h_neighbor_bound
  -- This contradicts positive definiteness
  intro hPD
  have h_pos := hPD.dotProduct_mulVec_pos hx_ne
  simp [star] at h_pos
  linarith

/-
**Corrected statement**: An indecomposable GCM of size ≥ 5 with positive-definite
    symmetrization has at most one branch vertex (vertex of degree ≥ 3).
    The proof uses the fact that if there were two branch vertices, we could
    construct a non-negative nonzero vector making the quadratic form ≤ 0,
    contradicting positive definiteness.
-/
theorem pos_numOfBranch_le_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C)
    (hP : (SymmMatrix C).PosDef) :
    numOfBranch C ≤ 1 := by
  contrapose! hP;
  obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp hP;
  exact not_posDef_of_two_branches C hGCM hI u v huv ( by simpa using hu ) ( by simpa using hv )
