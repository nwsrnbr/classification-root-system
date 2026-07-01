import Mathlib

variable {n : ℕ}

/-- A matrix `C` over `ℤ` is a **generalized Cartan matrix** if:
  1. Diagonal entries are 2.
  2. Off-diagonal entries are non-positive.
  3. `C i j = 0 ↔ C j i = 0` (symmetry of vanishing). -/
structure IsGeneralizedCartanMatrix {n : Type*} [DecidableEq n]
    (C : Matrix n n ℤ) : Prop where
  diag : ∀ i, C i i = 2
  off_diag_nonpos : ∀ i j, i ≠ j → C i j ≤ 0
  vanish_symm : ∀ i j, C i j = 0 ↔ C j i = 0

/-- A generalized Cartan matrix is **indecomposable** if there is no non-trivial partition
  of the index set into two subsets with all cross-entries zero.
  (Equivalently, the Dynkin diagram is connected.) -/
def IsIndecomposable {n : Type*} [DecidableEq n]
    (C : Matrix n n ℤ) : Prop :=
  ∀ (S : Set n), S ≠ ∅ → S ≠ Set.univ →
    ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0

/-
For i ≠ j with C i j ≠ 0 in a GCM, the product C i j * C j i ≥ 1.
-/
lemma edge_product_ge_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (i j : Fin n) (hij : i ≠ j) (h : C i j ≠ 0) :
    1 ≤ C i j * C j i := by
  have : C i j < 0 := by
    have := hGCM.off_diag_nonpos i j hij
    omega
  have : C j i < 0 := by
    have := hGCM.off_diag_nonpos j i hij.symm
    have := hGCM.vanish_symm j i
    omega
  nlinarith

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

/-- The set of neighbors of vertex `u` in the Dynkin diagram. -/
def neighborSet (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j

def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (neighborSet C i).card

/-- Two vertices are adjacent in the Dynkin diagram, excluding vertex `u`. -/
def adjExcl (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (i j : Fin n) : Prop :=
  i ≠ j ∧ i ≠ u ∧ j ≠ u ∧ C i j ≠ 0

/-- Vertex `w` is reachable from `v` in the Dynkin diagram with vertex `u` removed. -/
def reachExcl (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (v w : Fin n) : Prop :=
  Relation.ReflTransGen (adjExcl C u) v w

/-- The branch at `u` through `v`: all vertices reachable from `v` avoiding `u`. -/
def branchSet (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : Set (Fin n) :=
  {w | reachExcl C u v w}

/-- The number of vertices in the branch at `u` through `v`. -/
noncomputable def branchSize (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : ℕ :=
  Set.ncard (branchSet C u v)

/-! ### Potentially useful lemmas. -/

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

-- We have already formalized that the Dynkin diagram contains no cycles,
-- has at most one branching vertex, and that every vertex has degree at most 3.


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


-- All of the code below was formalized by you in a previous session.
-- Can you prove the result more simply using the lemmas above?

/-! ### Connected components of an induced subgraph (for the combinatorial core) -/

/-- Reachability using only edges with both endpoints inside `S`. -/
def reachIn {n : ℕ} (adj : Fin n → Fin n → Prop) (S : Finset (Fin n)) (w z : Fin n) : Prop :=
  Relation.ReflTransGen (fun i j => i ∈ S ∧ j ∈ S ∧ adj i j) w z

attribute [local instance] Classical.propDecidable

/-- The connected component of `w` inside `S`. -/
noncomputable def compIn {n : ℕ} (adj : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (w : Fin n) : Finset (Fin n) :=
  S.filter (fun z => reachIn adj S w z)

lemma reachIn_refl {n : ℕ} (adj : Fin n → Fin n → Prop) (S : Finset (Fin n)) (w : Fin n) :
    reachIn adj S w w := Relation.ReflTransGen.refl

lemma reachIn_symm {n : ℕ} {adj : Fin n → Fin n → Prop} (hsymm : ∀ i j, adj i j → adj j i)
    {S : Finset (Fin n)} {w z : Fin n} (h : reachIn adj S w z) : reachIn adj S z w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hsymm _ _ hbc.2.2⟩ ih

lemma reachIn_trans {n : ℕ} {adj : Fin n → Fin n → Prop} {S : Finset (Fin n)} {a b c : Fin n}
    (h1 : reachIn adj S a b) (h2 : reachIn adj S b c) : reachIn adj S a c :=
  Relation.ReflTransGen.trans h1 h2

/-
**Connected components partition.**  The set of components of `S` partitions `S`,
with no edges between distinct components.
-/
lemma exists_components {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (S : Finset (Fin n)) :
    ∃ P : Finset (Finset (Fin n)),
      (∀ C ∈ P, C ⊆ S) ∧
      (∀ C ∈ P, C.Nonempty) ∧
      (S = P.biUnion id) ∧
      (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
      (∀ C ∈ P, ∀ w ∈ C, ∀ z, z ∈ C ↔ (z ∈ S ∧ reachIn adj S w z)) ∧
      (∀ C ∈ P, ∀ w ∈ C, ∀ z ∈ S, adj w z → z ∈ C) := by
  refine' ⟨ Finset.image ( fun w => compIn adj S w ) ( Finset.filter ( fun w => w ∈ S ) Finset.univ ), _, _, _, _, _ ⟩ <;> simp +decide [ Finset.subset_iff ];
  · unfold compIn; aesop;
  · intro w hw; use w; simp +decide [ hw, compIn ] ;
    exact reachIn_refl adj S w;
  · ext w; simp [compIn];
    exact ⟨ fun hw => ⟨ w, hw, hw, reachIn_refl _ _ _ ⟩, by rintro ⟨ a, ha, hw, h ⟩ ; exact hw ⟩;
  · intro a ha b hb hab; rw [ Finset.disjoint_left ] ; contrapose! hab; simp_all +decide [ Finset.ext_iff, compIn ] ;
    obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hab; have := reachIn_symm hsymm hc₃; have := reachIn_trans hc₁.2 this; simp_all +decide [ reachIn_refl, reachIn_symm ] ;
    exact fun x hx => ⟨ fun h => reachIn_trans ( reachIn_symm hsymm this ) h, fun h => reachIn_trans this h ⟩;
  · simp +decide [ compIn ];
    constructor;
    · intro a ha w hw haw z hz;
      constructor <;> intro h;
      · exact reachIn_trans ( reachIn_symm hsymm haw ) h;
      · exact reachIn_trans haw h;
    · exact fun a ha w hw h₁ z hz h₂ => ⟨ hz, h₁.trans ( Relation.ReflTransGen.single ⟨ hw, hz, h₂ ⟩ ) ⟩

/-- A within-`S` path from `w` stays inside the component `compIn adj S w`. -/
lemma reachIn_confine {n : ℕ} {adj : Fin n → Fin n → Prop} {S : Finset (Fin n)} {w z : Fin n}
    (h : reachIn adj S w z) : reachIn adj (compIn adj S w) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hwb hbc ih =>
      have hbmem : b ∈ compIn adj S w :=
        Finset.mem_filter.2 ⟨hbc.1, hwb⟩
      have hcmem : c ∈ compIn adj S w :=
        Finset.mem_filter.2 ⟨hbc.2.1, hwb.tail hbc⟩
      exact ih.tail ⟨hbmem, hcmem, hbc.2.2⟩

/-- From a within-`K` path out of `r` to some `w ≠ r`, extract a neighbour `z` of
`r` lying in `K.erase r` that reaches `w` without using `r`. -/
lemma exists_first_neighbor {n : ℕ} {adj : Fin n → Fin n → Prop}
    {K : Finset (Fin n)} {r w : Fin n} (h : reachIn adj K r w) (hw : w ≠ r) :
    ∃ z, adj r z ∧ z ∈ K.erase r ∧ reachIn adj (K.erase r) z w := by
  induction h with
  | refl => exact absurd rfl hw
  | @tail b c hrb hbc ih =>
      rcases eq_or_ne b r with hbr | hbr
      · subst hbr
        exact ⟨c, hbc.2.2, Finset.mem_erase.2 ⟨hw, hbc.2.1⟩, Relation.ReflTransGen.refl⟩
      · obtain ⟨z, hz1, hz2, hz3⟩ := ih hbr
        exact ⟨z, hz1, hz2, hz3.tail ⟨Finset.mem_erase.2 ⟨hbr, hbc.1⟩,
          Finset.mem_erase.2 ⟨hw, hbc.2.1⟩, hbc.2.2⟩⟩

/-! ### Combinatorial core: rooted energy of a connected graph -/

/-
Square-sum of a weighting built from a partition splits as the root term plus
the per-component square sums.
-/
lemma combined_sq_sum {n : ℕ} (P : Finset (Finset (Fin n))) (S K : Finset (Fin n)) (r : Fin n)
    (a : ℝ) (f : Finset (Fin n) → Fin n → ℝ)
    (hrS : r ∉ S) (hK : K = insert r S) (hSP : S = P.biUnion id)
    (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
    (g : Fin n → ℝ)
    (hg : ∀ i, g i = if i = r then a else ∑ C ∈ P, if i ∈ C then f C i else 0) :
    ∑ i ∈ K, (g i) ^ 2 = a ^ 2 + ∑ C ∈ P, ∑ i ∈ C, (f C i) ^ 2 := by
  simp +decide [ *, Finset.sum_insert, Finset.sum_biUnion ];
  rw [ Finset.sum_insert ] <;> norm_num [ hrS, hSP ];
  · rw [ Finset.sum_biUnion ];
    · refine' Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun i hi => _;
      rw [ Finset.sum_eq_single C ] <;> simp_all +decide [ Finset.disjoint_left ];
      · grind;
      · exact fun D hD hDC hiD => False.elim <| hdisj _ hD _ hC hDC hiD hi;
    · exact fun x hx y hy hxy => hdisj x hx y hy hxy;
  · exact fun C hC => fun h => hrS <| hSP.symm ▸ Finset.mem_biUnion.mpr ⟨ C, hC, h ⟩

/-
Cross/quadratic term of a weighting built from a partition: with no edges
between distinct components, it splits into per-component quadratic terms plus the
root-to-component coupling.
-/
lemma combined_cross_sum {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (P : Finset (Finset (Fin n))) (S K : Finset (Fin n)) (r : Fin n)
    (a : ℝ) (f : Finset (Fin n) → Fin n → ℝ)
    (hrS : r ∉ S) (hK : K = insert r S) (hSP : S = P.biUnion id)
    (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
    (hsupp : ∀ C ∈ P, ∀ i, i ∉ C → f C i = 0)
    (hcross : ∀ C ∈ P, ∀ i ∈ C, ∀ j ∈ S, adj i j → j ∈ C)
    (g : Fin n → ℝ)
    (hg : ∀ i, g i = if i = r then a else ∑ C ∈ P, if i ∈ C then f C i else 0) :
    ∑ i ∈ K, ∑ j ∈ K, (if adj i j then g i * g j else 0) =
      (∑ C ∈ P, ∑ i ∈ C, ∑ j ∈ C, (if adj i j then f C i * f C j else 0))
        + 2 * a * ∑ C ∈ P, ∑ i ∈ C, (if adj r i then f C i else 0) := by
  -- Using the definition of $g$ from $hg$, we can expand the sums and simplify.
  have h_expand : (∑ i ∈ K, ∑ j ∈ K, if adj i j then g i * g j else 0) = (∑ i ∈ S, ∑ j ∈ S, if adj i j then (∑ C ∈ P, (if i ∈ C then f C i else 0)) * (∑ D ∈ P, (if j ∈ D then f D j else 0)) else 0) + 2 * a * (∑ i ∈ S, if adj r i then (∑ C ∈ P, (if i ∈ C then f C i else 0)) else 0) := by
    simp +decide [ hK, hg, Finset.sum_insert hrS ];
    simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, hirr, hsymm, hrS, Finset.sum_ite ] ; ring;
    simp +decide [ Finset.filter_eq', Finset.filter_ne', hrS, hirr, hsymm, Finset.sum_filter, Finset.sum_add_distrib, mul_two, add_assoc ] ; ring!;
    grind +qlia;
  convert h_expand using 2;
  · -- Apply the disjointness of the components to split the sum.
    have h_split_sum : ∑ i ∈ S, ∑ j ∈ S, (if adj i j then (∑ C ∈ P, (if i ∈ C then f C i else 0)) * (∑ D ∈ P, (if j ∈ D then f D j else 0)) else 0) = ∑ C ∈ P, ∑ i ∈ C, ∑ j ∈ C, (if adj i j then (∑ D ∈ P, (if i ∈ D then f D i else 0)) * (∑ E ∈ P, (if j ∈ E then f E j else 0)) else 0) := by
      rw [ hSP, Finset.sum_biUnion ];
      · refine' Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun i hi => _;
        rw [ ← Finset.sum_subset ( show C ⊆ P.biUnion id from fun x hx => Finset.mem_biUnion.mpr ⟨ C, hC, hx ⟩ ) ];
        grind;
      · exact fun x hx y hy hxy => hdisj x hx y hy hxy;
    convert h_split_sum.symm using 3;
    refine' Finset.sum_congr rfl fun j hj => _;
    rw [ Finset.sum_eq_single ‹_›, Finset.sum_eq_single ‹_› ] <;> simp +contextual [ * ];
    · exact fun C hC hne hjC => False.elim <| Finset.disjoint_left.mp ( hdisj _ hC _ ‹_› hne ) hjC hj;
    · exact fun C hC hne hi => hsupp C hC _ ( fun hi' => Finset.disjoint_left.mp ( hdisj _ hC _ ‹_› hne ) hi' ‹_› );
  · simp +decide [ Finset.sum_ite, Finset.filter_congr, hSP ];
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine' Or.inl ( Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst ⟩ ) _ _ _ _ ) <;> simp +contextual [ hSP ];
    · exact fun a ha₁ ha₂ ha₃ => ⟨ _, ha₁, ha₂ ⟩;
    · bound;
    · exact fun b x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ _, _, ⟨ hx₄, hx₅, hx₃ ⟩, rfl ⟩

/-
Sum of squares of the indicator of `V` is `|V|`.
-/
lemma indicator_sq_sum {n : ℕ} (V : Finset (Fin n)) :
    ∑ i, (if i ∈ V then (1:ℝ) else 0) ^ 2 = (V.card : ℝ) := by
  norm_num [ Finset.sum_ite ]

/-
Weight-one edge form of the indicator of `V` restricts to `V`.
-/
lemma indicator_cross_sum {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (V : Finset (Fin n)) :
    ∑ i, ∑ j, (if adj i j then (if i ∈ V then (1:ℝ) else 0) * (if j ∈ V then (1:ℝ) else 0) else 0)
      = ∑ i ∈ V, ∑ j ∈ V, (if adj i j then (1:ℝ) else 0) := by
  simp +contextual [ ← Finset.sum_filter, Finset.sum_ite ];
  exact Finset.sum_congr rfl fun x hx => by congr; ext y; aesop;

/-
Edge form on `insert r B` (with `r ∉ B`) splits into the `B`-edges plus twice
the number of edges from `r` into `B`.
-/
lemma insert_root_edge_sum {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (B : Finset (Fin n)) (r : Fin n) (hr : r ∉ B) :
    ∑ i ∈ insert r B, ∑ j ∈ insert r B, (if adj i j then (1:ℝ) else 0)
      = (∑ i ∈ B, ∑ j ∈ B, (if adj i j then (1:ℝ) else 0))
        + 2 * ∑ j ∈ B, (if adj r j then (1:ℝ) else 0) := by
  simp +decide [ Finset.sum_insert hr, Finset.sum_add_distrib, two_mul, hirr ];
  rw [ show ( Finset.filter ( fun x => adj x r ) B ) = Finset.filter ( fun x => adj r x ) B from Finset.filter_congr fun x hx => ⟨ fun h => hsymm _ _ h, fun h => hsymm _ _ h ⟩ ] ; ring

/-
Scalar arithmetic core of the induction step: combining the per-component
energy lower bounds yields the root bound, reducing to a sum-of-squares estimate.
-/
lemma energy_scalar {ix : Type*} (N : ℕ) (hN : 2 ≤ N) (P : Finset ix) (t : ix → ℕ)
    (Sq Ad R : ix → ℝ)
    (hsum : ∑ C ∈ P, (t C : ℝ) = (N : ℝ) - 1)
    (hAS : ∀ C ∈ P, -((t C : ℝ) / (t C + 1)) ≤ Ad C - 2 * Sq C)
    (hR : ∀ C ∈ P, (t C : ℝ) / (t C + 1) ≤ R C) :
    (N : ℝ) / (N + 1) ≤
      2 * ((N : ℝ) / (N + 1))
        - 2 * (((N : ℝ) / (N + 1)) ^ 2
            + ∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) ^ 2 * Sq C)
        + ((∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) ^ 2 * Ad C)
            + 2 * ((N : ℝ) / (N + 1)) * ∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) * R C) := by
  -- Combine the two component sums into one and bound termwise.
  suffices h_sum_bound : (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (Ad C - 2 * Sq C) + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * R C)) ≥ (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (-(t C / (t C + 1 : ℝ))) + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * (t C / (t C + 1 : ℝ)))) by
    -- Simplify the per-term right side in closed form.
    have h_simplify : (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (-(t C / (t C + 1 : ℝ))) + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * (t C / (t C + 1 : ℝ)))) = (2 * N * (∑ C ∈ P, (t C : ℝ)) - (∑ C ∈ P, (t C : ℝ) ^ 2) - (∑ C ∈ P, (t C : ℝ))) / (N + 1) ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ];
      rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_sub_distrib ] ; rw [ ← Finset.sum_sub_distrib ] ; rw [ Finset.sum_div ] ; congr ; ext x ; ring;
      -- Combine like terms and simplify the expression.
      field_simp
      ring;
    -- Apply the inequality $\sum_{C \in P} t_C^2 \leq (\sum_{C \in P} t_C)^2$.
    have h_sum_sq : (∑ C ∈ P, (t C : ℝ) ^ 2) ≤ (∑ C ∈ P, (t C : ℝ)) ^ 2 := by
      simpa only [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun a _ => Nat.cast_nonneg ( t a ) ) hi ) ( Nat.cast_nonneg ( t i ) );
    simp_all +decide [ Finset.sum_add_distrib, mul_sub ];
    field_simp at *;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_div_assoc ] at * ; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ N ) ];
  exact add_le_add ( Finset.sum_le_sum fun C hC => mul_le_mul_of_nonneg_left ( hAS C hC ) ( sq_nonneg _ ) ) ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun C hC => mul_le_mul_of_nonneg_left ( hR C hC ) ( by positivity ) ) ( by positivity ) )

/-
**Rooted energy bound (strengthened).**  For a finite connected graph (`adj`,
symmetric, irreflexive) on a vertex set `K` with a chosen root `r`, there is a
nonnegative weighting `y` supported on `K`, with `y r = |K|/(|K|+1)`, whose rooted
energy `2 y_r - 2 Σ y_i² + Σ [adj i j] y_i y_j` is at least `|K|/(|K|+1)`.  Tight
for a path rooted at an endpoint; the heart of the branch inequality.
-/
set_option maxHeartbeats 4000000 in
lemma branch_energy_strong {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (K : Finset (Fin n)) (r : Fin n) (hr : r ∈ K)
    (hconn : ∀ w ∈ K, reachIn adj K r w) :
    ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, i ∉ K → y i = 0) ∧
      y r = (K.card : ℝ) / (K.card + 1) ∧
      (K.card : ℝ) / (K.card + 1) ≤
        2 * y r - 2 * (∑ i ∈ K, (y i) ^ 2)
          + (∑ i ∈ K, ∑ j ∈ K, if adj i j then y i * y j else 0) := by
  -- By induction on the size of the set $K$.
  have h_ind_step : ∀ N : ℕ, ∀ (K : Finset (Fin n)), K.card = N → ∀ r ∈ K, ∀ (hconn : ∀ w ∈ K, reachIn adj K r w), ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i ∉ K, y i = 0) ∧ y r = N / (N + 1) ∧ (N : ℝ) / (N + 1) ≤ 2 * y r - 2 * ∑ i ∈ K, y i ^ 2 + ∑ i ∈ K, ∑ j ∈ K, (if adj i j then y i * y j else 0) := by
    intro N K hK r hr hconn
    induction' N using Nat.strong_induction_on with N ih generalizing K r;
    by_cases hN : N ≤ 1;
    · interval_cases N <;> simp_all +decide;
      refine' ⟨ fun i => if i = r then 1 / 2 else 0, _, _, _, _ ⟩ <;> norm_num [ hr, hK ];
      · intro i; split_ifs <;> norm_num;
      · exact fun i hi => by rintro rfl; exact hi hr;
      · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num;
    · obtain ⟨P, hP⟩ := exists_components adj hsymm (K.erase r);
      -- For each component $C \in P$, choose a vertex $r_C \in C$ such that $adj r r_C$.
      obtain ⟨r_C, hr_C⟩ : ∃ r_C : Finset (Fin n) → Fin n, ∀ C ∈ P, r_C C ∈ C ∧ adj r (r_C C) := by
        have h_exists_r_C : ∀ C ∈ P, ∃ w ∈ C, adj r w := by
          intro C hC
          obtain ⟨w, hw⟩ : ∃ w ∈ C, reachIn adj K r w := by
            exact Exists.elim ( hP.2.1 C hC ) fun w hw => ⟨ w, hw, hconn w ( Finset.mem_of_mem_erase ( hP.1 C hC hw ) ) ⟩;
          have := exists_first_neighbor hw.2 (by
          grind +revert);
          grind;
        exact ⟨ fun C => if hC : C ∈ P then Classical.choose ( h_exists_r_C C hC ) else r, fun C hC => by simpa [ hC ] using Classical.choose_spec ( h_exists_r_C C hC ) ⟩;
      -- For each component $C \in P$, apply the induction hypothesis to obtain a weighting $y_C$.
      obtain ⟨y_C, hy_C⟩ : ∃ y_C : Finset (Fin n) → (Fin n → ℝ), (∀ C ∈ P, (∀ i, 0 ≤ y_C C i) ∧ (∀ i ∉ C, y_C C i = 0) ∧ y_C C (r_C C) = C.card / (C.card + 1) ∧ (C.card : ℝ) / (C.card + 1) ≤ 2 * y_C C (r_C C) - 2 * ∑ i ∈ C, y_C C i ^ 2 + ∑ i ∈ C, ∑ j ∈ C, (if adj i j then y_C C i * y_C C j else 0)) := by
        have h_ind_step : ∀ C ∈ P, ∃ y_C : Fin n → ℝ, (∀ i, 0 ≤ y_C i) ∧ (∀ i ∉ C, y_C i = 0) ∧ y_C (r_C C) = C.card / (C.card + 1) ∧ (C.card : ℝ) / (C.card + 1) ≤ 2 * y_C (r_C C) - 2 * ∑ i ∈ C, y_C i ^ 2 + ∑ i ∈ C, ∑ j ∈ C, (if adj i j then y_C i * y_C j else 0) := by
          intros C hC
          apply ih (C.card) (by
          exact lt_of_le_of_lt ( Finset.card_le_card ( hP.1 C hC ) ) ( by rw [ Finset.card_erase_of_mem hr, hK ] ; omega )) C rfl (r_C C) (hr_C C hC).left (by
          intro w hw
          have h_reach : reachIn adj (K.erase r) (r_C C) w := by
            grind +splitIndPred
          have h_reach_C : reachIn adj C (r_C C) w := by
            convert reachIn_confine h_reach using 1;
            grind +locals
          exact h_reach_C);
        choose! y_C hy_C using h_ind_step;
        use y_C;
      -- Define the weighting $y$ for the entire set $K$.
      use fun i => if i = r then (N : ℝ) / (N + 1) else ∑ C ∈ P, (if i ∈ C then ((C.card + 1) / (N + 1)) * y_C C i else 0);
      refine' ⟨ _, _, _, _ ⟩;
      · simp +zetaDelta at *;
        intro i; split_ifs <;> [ exact div_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ; exact Finset.sum_nonneg fun C hC => by split_ifs <;> [ exact mul_nonneg ( div_nonneg ( by positivity ) ( by positivity ) ) ( hy_C C hC |>.1 i ) ; exact le_rfl ] ] ;
      · simp +contextual [ Finset.subset_iff ];
        intro i hi; split_ifs <;> simp_all +decide [ Finset.subset_iff ] ;
        exact Finset.sum_eq_zero fun C hC => if_neg fun hiC => hi <| hP.1 C hC hiC |>.2;
      · simp +decide [ hr ];
      · convert energy_scalar N ( by linarith ) P ( fun C => C.card ) ( fun C => ∑ i ∈ C, y_C C i ^ 2 ) ( fun C => ∑ i ∈ C, ∑ j ∈ C, if adj i j then y_C C i * y_C C j else 0 ) ( fun C => ∑ i ∈ C, if adj r i then y_C C i else 0 ) _ _ _ using 1;
        · congr! 1;
          · convert combined_sq_sum P ( K.erase r ) K r ( N / ( N + 1 ) ) ( fun C i => ( C.card + 1 : ℝ ) / ( N + 1 ) * y_C C i ) _ _ _ _ _ using 1;
            rotate_right;
            use fun i => if i = r then N / ( N + 1 ) else ∑ C ∈ P, if i ∈ C then ( C.card + 1 : ℝ ) / ( N + 1 ) * y_C C i else 0;
            · simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', Finset.mul_sum _ _ _, mul_pow ];
            · simp +decide [ hr ];
            · rw [ Finset.insert_erase hr ];
            · exact hP.2.2.1;
            · exact hP.2.2.2.1;
          · convert combined_cross_sum adj hsymm hirr P ( K.erase r ) K r ( N / ( N + 1 ) ) ( fun C i => ( C.card + 1 : ℝ ) / ( N + 1 ) * y_C C i ) _ _ _ _ _ _ using 1;
            any_goals tauto;
            · constructor;
              · intro h g hg;
                convert h using 1;
                · exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ hg i, hg j ] ;
                · simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul, sq ];
              · intro h;
                convert h _ fun i => rfl using 1;
                simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
                exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
            · simp +decide [ hr ];
            · rw [ Finset.insert_erase hr ];
            · exact hP.2.2.2.1;
            · exact fun C hC i hi => mul_eq_zero_of_right _ ( hy_C C hC |>.2.1 i hi );
        · have h_sum_card : ∑ C ∈ P, C.card = (K.erase r).card := by
            rw [ hP.2.2.1, Finset.card_biUnion ];
            · rfl;
            · exact fun x hx y hy hxy => hP.2.2.2.1 x hx y hy hxy;
          rw [ ← Nat.cast_sum, h_sum_card, Finset.card_erase_of_mem hr, hK ];
          rw [ Nat.cast_pred ( by linarith ) ];
        · grind;
        · intro C hC; specialize hy_C C hC; specialize hr_C C hC; simp_all +decide [ Finset.sum_ite ] ;
          refine' le_trans _ ( Finset.single_le_sum ( fun x _ => hy_C.1 x ) ( Finset.mem_filter.mpr ⟨ hr_C.1, hr_C.2 ⟩ ) ) ; aesop;
  exact h_ind_step _ _ rfl _ hr hconn

lemma branch_energy {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (K : Finset (Fin n)) (r : Fin n) (hr : r ∈ K)
    (hconn : ∀ w ∈ K, Relation.ReflTransGen (fun i j => i ∈ K ∧ j ∈ K ∧ adj i j) r w) :
    ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, i ∉ K → y i = 0) ∧
      (K.card : ℝ) / (K.card + 1) ≤
        2 * y r - 2 * (∑ i ∈ K, (y i) ^ 2)
          + (∑ i ∈ K, ∑ j ∈ K, if adj i j then y i * y j else 0) := by
  obtain ⟨y, hy0, hsupp, _, hE⟩ := branch_energy_strong adj hsymm hirr K r hr hconn
  exact ⟨y, hy0, hsupp, hE⟩

/-! ### Basic algebraic facts about `SymmMatrix` -/

@[simp] lemma SymmMatrix_diag (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    SymmMatrix C i i = 2 := by
  simp [SymmMatrix]

lemma SymmMatrix_offdiag (C : Matrix (Fin n) (Fin n) ℤ) {i j : Fin n} (h : i ≠ j) :
    SymmMatrix C i j = -Real.sqrt (C i j * C j i) := by
  simp [SymmMatrix, h]

lemma SymmMatrix_offdiag_nonpos (C : Matrix (Fin n) (Fin n) ℤ) {i j : Fin n} (h : i ≠ j) :
    SymmMatrix C i j ≤ 0 := by
  rw [SymmMatrix_offdiag C h]; simp [Real.sqrt_nonneg]

lemma SymmMatrix_symm (C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    SymmMatrix C i j = SymmMatrix C j i := by
  rcases eq_or_ne i j with h | h
  · subst h; rfl
  · rw [SymmMatrix_offdiag C h, SymmMatrix_offdiag C h.symm, mul_comm]

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

/-
For a degree-3 vertex `u` in a positive-definite Dynkin graph, with the three
branches having `a`, `b`, `c` vertices (excluding `u`), one has
`1/(a+1) + 1/(b+1) + 1/(c+1) > 1`.

NOTE (statement correction): the original statement below used natural-number
division in the conclusion.  In `ℕ`, `1 / (k + 1) = 0` for every `k ≥ 1`, and
since every branch always contains its own root vertex `vᵢ` we have
`branchSize C u vᵢ ≥ 1`.  Hence every summand is `0`, the sum is `0`, and the
conclusion `0 > 1` is false (the hypotheses are satisfiable, e.g. the `D₄`
diagram).  The intended statement, matching the accompanying `.tex` proof, uses
real-valued division; that corrected version is stated and proved below, and the
original (false) statement is preserved as a comment.
-/

/-
-- ORIGINAL (FALSE as written: ℕ division makes every term 0, so the sum is 0):
theorem branciSize_inequality (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    1 / (branchSize C u v₁ + 1) +
    1 / (branchSize C u v₂ + 1) +
    1 / (branchSize C u v₃ + 1) > 1 := by
  sorry
-/

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

/-- The branch at `u` through `v`, as a `Finset`. -/
noncomputable def branchFinset (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : Finset (Fin n) :=
  (branchSet C u v).toFinset

@[simp] lemma mem_branchFinset (C : Matrix (Fin n) (Fin n) ℤ) (u v w : Fin n) :
    w ∈ branchFinset C u v ↔ reachExcl C u v w := by
  simp [branchFinset, branchSet]

lemma branchSize_eq_card (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) :
    branchSize C u v = (branchFinset C u v).card := by
  rw [branchSize, branchFinset, Set.ncard_eq_toFinset_card']

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
  obtain ⟨y, hy0, hsupp, hE⟩ :=
    branch_energy (Gadj C) (Gadj_symm C hGCM) (Gadj_irr C) (branchFinset C u v) v hr
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
A finite connected graph on `K` has at least `|K| - 1` edges (counted as the
real-valued ordered-pair sum `≥ 2(|K|-1)`).
-/
set_option maxHeartbeats 4000000 in
lemma connected_edge_bound {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (K : Finset (Fin n)) (r : Fin n) (hr : r ∈ K)
    (hconn : ∀ w ∈ K, reachIn adj K r w) :
    2 * ((K.card : ℝ) - 1) ≤ ∑ i ∈ K, ∑ j ∈ K, (if adj i j then (1:ℝ) else 0) := by
  revert K r hr hconn;
  intro K r hr hconn; have := hconn r hr; induction' K using Finset.strongInduction with K ih generalizing r;
  obtain ⟨P, hP⟩ := exists_components adj hsymm (K.erase r);
  -- Apply `combined_cross_sum` with `a := 1` and `f C := fun i => if i ∈ C then (1:ℝ) else 0`.
  have h_combined : ∑ i ∈ K, ∑ j ∈ K, (if adj i j then (1 : ℝ) else 0) = ∑ C ∈ P, ∑ i ∈ C, ∑ j ∈ C, (if adj i j then (1 : ℝ) else 0) + 2 * ∑ C ∈ P, ∑ i ∈ C, (if adj r i then (1 : ℝ) else 0) := by
    convert combined_cross_sum adj hsymm hirr P ( K.erase r ) K r 1 ( fun C i => if i ∈ C then ( 1 : ℝ ) else 0 ) _ _ _ _ _ _ using 1;
    any_goals tauto;
    · constructor <;> intro h;
      · convert combined_cross_sum adj hsymm hirr P ( K.erase r ) K r 1 ( fun C i => if i ∈ C then ( 1 : ℝ ) else 0 ) _ _ _ _ _ _ using 1;
        all_goals norm_num;
        · rw [ Finset.insert_erase hr ];
        · exact hP.2.2.1;
        · exact hP.2.2.2.1;
        · grind;
      · convert h ( fun i => if i = r then 1 else ∑ C ∈ P, if i ∈ C then if i ∈ C then 1 else 0 else 0 ) ( fun i => rfl ) using 1;
        · refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => _;
          by_cases hi' : i = r <;> by_cases hj' : j = r <;> simp +decide [ hi', hj' ];
          · rw [ Finset.sum_eq_single ( Classical.choose ( Finset.mem_biUnion.mp ( hP.2.2.1 ▸ Finset.mem_erase_of_ne_of_mem hj' hj ) ) ) ] <;> simp +contextual [ Classical.choose_spec ( Finset.mem_biUnion.mp ( hP.2.2.1 ▸ Finset.mem_erase_of_ne_of_mem hj' hj ) ) ]; all_goals grind;
          · simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
            rw [ Finset.card_eq_one.mpr ];
            · norm_num;
            · obtain ⟨ C, hC ⟩ := Finset.mem_biUnion.mp ( hP.2.2.1 ▸ Finset.mem_erase_of_ne_of_mem hi' hi ) ; use C; ext; simp +decide [ hC ] ;
              exact ⟨ fun h => Classical.not_not.1 fun h' => Finset.disjoint_left.mp ( hP.2.2.2.1 _ h.1 _ hC.1 h' ) h.2 hC.2, fun h => h.symm ▸ hC ⟩;
          · simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_ne', Finset.filter_eq', hi', hj' ];
            rw [ Finset.card_eq_one.mpr, Finset.card_eq_one.mpr ] <;> norm_num;
            · obtain ⟨ C, hC ⟩ := Finset.mem_biUnion.mp ( hP.2.2.1 ▸ Finset.mem_erase_of_ne_of_mem hj' hj ) ; use C; ext; simp +decide [ hC ] ;
              exact ⟨ fun h => Classical.not_not.1 fun h' => Finset.disjoint_left.mp ( hP.2.2.2.1 _ h.1 _ hC.1 h' ) h.2 hC.2, fun h => h.symm ▸ hC ⟩;
            · obtain ⟨ C, hC ⟩ := Finset.mem_biUnion.mp ( hP.2.2.1 ▸ Finset.mem_erase_of_ne_of_mem hi' hi );
              use C; ext; simp [hC];
              exact ⟨ fun h => Classical.not_not.1 fun h' => Finset.disjoint_left.mp ( hP.2.2.2.1 _ h.1 _ hC.1 h' ) h.2 hC.2, fun h => h.symm ▸ hC ⟩;
        · simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
          exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ) ( congr_arg _ ( Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ) );
    · simp +decide [ hr ];
    · rw [ Finset.insert_erase hr ];
    · exact hP.2.2.2.1;
    · grind +qlia;
  -- For each component $C \in P$, we have $2 * (C.card - 1) \leq \sum_{i \in C} \sum_{j \in C} (if adj i j then 1 else 0)$.
  have h_component : ∀ C ∈ P, 2 * (C.card - 1 : ℝ) ≤ ∑ i ∈ C, ∑ j ∈ C, (if adj i j then (1 : ℝ) else 0) := by
    intro C hC;
    -- Since $C$ is a component of $K.erase r$, it is connected.
    have h_connected : ∀ w ∈ C, reachIn adj C (Classical.choose (hP.2.1 C hC)) w := by
      intro w hw
      have h_reach : reachIn adj (K.erase r) (Classical.choose (hP.2.1 C hC)) w := by
        grind +splitIndPred;
      convert reachIn_confine h_reach using 1;
      grind +locals;
    grind +splitIndPred;
  -- For each component $C \in P$, we have $\sum_{i \in C} (if adj r i then 1 else 0) \geq 1$.
  have h_component_adj : ∀ C ∈ P, ∑ i ∈ C, (if adj r i then (1 : ℝ) else 0) ≥ 1 := by
    intro C hC
    obtain ⟨w, hw⟩ : ∃ w ∈ C, adj r w := by
      obtain ⟨w, hw⟩ : ∃ w ∈ C, reachIn adj K r w := by
        exact Exists.elim ( hP.2.1 C hC ) fun w hw => ⟨ w, hw, hconn w ( Finset.mem_of_mem_erase ( hP.1 C hC hw ) ) ⟩;
      have := exists_first_neighbor hw.2 (by
      grind +splitImp);
      grind;
    exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun i _ => by positivity ) hw.1 );
  have h_sum_card : ∑ C ∈ P, C.card = (K.erase r).card := by
    rw [ hP.2.2.1, Finset.card_biUnion ] ; aesop;
    exact fun x hx y hy hxy => hP.2.2.2.1 x hx y hy hxy;
  have := Finset.sum_le_sum h_component; have := Finset.sum_le_sum h_component_adj; simp_all +decide [ Finset.sum_add_distrib, mul_sub ] ;
  rw [ ← Finset.mul_sum _ _ _ ] at * ; norm_cast at * ; simp_all +decide [ Finset.sum_add_distrib, mul_add ] ;
  rw [ ← Finset.card_erase_add_one hr ] ; linarith [ show Finset.card ( P.biUnion id ) = Finset.card ( K.erase r ) from hP.2.2.1 ▸ rfl ] ;

/-
The matrix quadratic form is bounded above by the simple-graph (`Gadj`,
weight-one) form for nonnegative vectors, since every bond `√(C i j * C j i) ≥ 1`.
-/
lemma form_le_Gadj (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    dotProduct (star x) ((SymmMatrix C).mulVec x) ≤
      2 * (∑ i, (x i) ^ 2) - ∑ i, ∑ j, (if Gadj C i j then x i * x j else 0) := by
  simp +decide [ Matrix.mulVec, dotProduct ];
  -- Apply the inequality term by term to the double sum.
  have h_term_by_term : ∀ i j, x i * SymmMatrix C i j * x j ≤ (if i = j then 2 * x i * x j else 0) - (if Gadj C i j then x i * x j else 0) := by
    intro i j; split_ifs <;> simp_all +decide [ SymmMatrix ] ;
    · exact absurd ‹Gadj C j j› ( by unfold Gadj; aesop );
    · linarith;
    · exact mul_le_mul_of_nonneg_right ( le_mul_of_one_le_right ( hx i ) ( by exact_mod_cast SymmMatrix_bond_ge_one C hGCM ‹_› ( by unfold Gadj at *; tauto ) ) ) ( hx j );
    · exact mul_nonneg ( mul_nonneg ( hx i ) ( Real.sqrt_nonneg _ ) ) ( hx j );
  convert Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_term_by_term i j using 1 ; simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, sq ] ; ring!;
  simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, mul_assoc, sq ];
  rw [ Finset.mul_sum _ _ _ ]

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
    ∑ i, (if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) ^ 2
      = 1 + (∑ i ∈ branchFinset C u v₁, (y₁ i) ^ 2)
          + (∑ i ∈ branchFinset C u v₂, (y₂ i) ^ 2)
          + (∑ i ∈ branchFinset C u v₃, (y₃ i) ^ 2) := by
  have h_split : ∀ i, i ≠ u → ((y₁ i + y₂ i + y₃ i) ^ 2 = (y₁ i) ^ 2 + (y₂ i) ^ 2 + (y₃ i) ^ 2) := by
    intro i hi; by_cases hi1 : i ∈ branchFinset C u v₁ <;> by_cases hi2 : i ∈ branchFinset C u v₂ <;> by_cases hi3 : i ∈ branchFinset C u v₃ <;> simp_all +decide [ Finset.disjoint_left ] ;
  simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', h_split ];
  rw [ Finset.sum_congr rfl fun i hi => if hiu : i = u then by aesop else h_split i hiu ] ; norm_num [ Finset.sum_add_distrib, add_assoc ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( branchFinset C u v₁ ) ) fun i hi₁ hi₂ => by aesop, ← Finset.sum_subset ( Finset.subset_univ ( branchFinset C u v₂ ) ) fun i hi₁ hi₂ => by aesop, ← Finset.sum_subset ( Finset.subset_univ ( branchFinset C u v₃ ) ) fun i hi₁ hi₂ => by aesop ] ; aesop;

/-
Cross (quadratic) term of the assembled test vector.
-/
set_option maxHeartbeats 4000000 in
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
        (if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) *
        (if j = u then (1:ℝ) else y₁ j + y₂ j + y₃ j) else 0))
      = (∑ i ∈ branchFinset C u v₁, ∑ j ∈ branchFinset C u v₁,
            if Gadj C i j then y₁ i * y₁ j else 0)
        + (∑ i ∈ branchFinset C u v₂, ∑ j ∈ branchFinset C u v₂,
            if Gadj C i j then y₂ i * y₂ j else 0)
        + (∑ i ∈ branchFinset C u v₃, ∑ j ∈ branchFinset C u v₃,
            if Gadj C i j then y₃ i * y₃ j else 0)
        + 2 * (y₁ v₁ + y₂ v₂ + y₃ v₃) := by
  have h_split : ∀ i, i ≠ u → ∀ j, j ≠ u → (if Gadj C i j then (y₁ i + y₂ i + y₃ i) * (y₁ j + y₂ j + y₃ j) else 0) = (if Gadj C i j then y₁ i * y₁ j else 0) + (if Gadj C i j then y₂ i * y₂ j else 0) + (if Gadj C i j then y₃ i * y₃ j else 0) := by
    intros i hi j hj
    by_cases h_adj : Gadj C i j;
    · by_cases hi1 : i ∈ branchFinset C u v₁ <;> by_cases hj1 : j ∈ branchFinset C u v₁ <;> simp_all +decide [ Finset.disjoint_left ];
      · grind +locals;
      · grind +locals;
      · grind +locals;
    · simp [h_adj];
  have h_split : (∑ i, ∑ j, if Gadj C i j then (if i = u then 1 else y₁ i + y₂ i + y₃ i) * (if j = u then 1 else y₁ j + y₂ j + y₃ j) else 0) = (∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u, (if Gadj C i j then y₁ i * y₁ j else 0) + ∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u, (if Gadj C i j then y₂ i * y₂ j else 0) + ∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u, (if Gadj C i j then y₃ i * y₃ j else 0)) + 2 * (∑ i ∈ Finset.univ.erase u, if Gadj C u i then (y₁ i + y₂ i + y₃ i) else 0) := by
    have h_split : (∑ i, ∑ j, if Gadj C i j then (if i = u then 1 else y₁ i + y₂ i + y₃ i) * (if j = u then 1 else y₁ j + y₂ j + y₃ j) else 0) = (∑ i ∈ Finset.univ.erase u, ∑ j ∈ Finset.univ.erase u, (if Gadj C i j then (y₁ i + y₂ i + y₃ i) * (y₁ j + y₂ j + y₃ j) else 0)) + (∑ i ∈ Finset.univ.erase u, if Gadj C u i then (y₁ i + y₂ i + y₃ i) else 0) + (∑ j ∈ Finset.univ.erase u, if Gadj C j u then (y₁ j + y₂ j + y₃ j) else 0) := by
      simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', Finset.sum_add_distrib, add_assoc ];
      simp +decide [ Finset.sum_ite, Finset.filter_erase, Gadj_irr ] ; ring!;
      rw [ show ( ∑ x : Fin n, ↑ ( if Gadj C x u then { u } else ∅ : Finset ( Fin n ) ).card * y₁ x ) = ∑ x ∈ Finset.filter ( fun x => Gadj C x u ) Finset.univ, y₁ x from ?_, show ( ∑ x : Fin n, ↑ ( if Gadj C x u then { u } else ∅ : Finset ( Fin n ) ).card * y₂ x ) = ∑ x ∈ Finset.filter ( fun x => Gadj C x u ) Finset.univ, y₂ x from ?_, show ( ∑ x : Fin n, ↑ ( if Gadj C x u then { u } else ∅ : Finset ( Fin n ) ).card * y₃ x ) = ∑ x ∈ Finset.filter ( fun x => Gadj C x u ) Finset.univ, y₃ x from ?_ ] ; ring!;
      · rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
      · rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
      · rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
    rw [ h_split ];
    rw [ Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ‹∀ i : Fin n, i ≠ u → ∀ j : Fin n, j ≠ u → ( if Gadj C i j then ( y₁ i + y₂ i + y₃ i ) * ( y₁ j + y₂ j + y₃ j ) else 0 ) = ( ( if Gadj C i j then y₁ i * y₁ j else 0 ) + if Gadj C i j then y₂ i * y₂ j else 0 ) + if Gadj C i j then y₃ i * y₃ j else 0› i ( Finset.ne_of_mem_erase hi ) j ( Finset.ne_of_mem_erase hj ) ] ; norm_num [ Finset.sum_add_distrib, two_mul ] ; ring;
    rw [ show ( ∑ x : Fin n, if Gadj C x u then y₁ x + y₂ x + y₃ x else 0 ) = ( ∑ x : Fin n, if Gadj C u x then y₁ x + y₂ x + y₃ x else 0 ) from ?_ ] ; ring;
    congr! 1;
    grind +suggestions;
  have h_split : (∑ i ∈ Finset.univ.erase u, if Gadj C u i then (y₁ i + y₂ i + y₃ i) else 0) = (y₁ v₁ + y₂ v₂ + y₃ v₃) := by
    rw [ ← Finset.sum_subset ( show { v₁, v₂, v₃ } ⊆ Finset.univ.erase u from ?_ ) ];
    · have h_distinct : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
        exact ⟨ by rintro rfl; exact Finset.disjoint_left.mp hd12 ( mem_branchFinset C u v₁ v₁ |>.mpr Relation.ReflTransGen.refl ) ( mem_branchFinset C u v₁ v₁ |>.mpr Relation.ReflTransGen.refl ), by rintro rfl; exact Finset.disjoint_left.mp hd13 ( mem_branchFinset C u v₁ v₁ |>.mpr Relation.ReflTransGen.refl ) ( mem_branchFinset C u v₁ v₁ |>.mpr Relation.ReflTransGen.refl ), by rintro rfl; exact Finset.disjoint_left.mp hd23 ( mem_branchFinset C u v₂ v₂ |>.mpr Relation.ReflTransGen.refl ) ( mem_branchFinset C u v₂ v₂ |>.mpr Relation.ReflTransGen.refl ) ⟩;
      simp +decide [ *, Finset.sum_pair, Finset.sum_singleton ];
      simp +decide [ ← neighbor_iff_Gadj, htrip ];
      rw [ hs2 v₁, hs3 v₁, hs1 v₂, hs3 v₂, hs1 v₃, hs2 v₃ ] <;> norm_num;
      grind +locals;
      exact fun h => Finset.disjoint_left.mp hd23 ( ( mem_branchFinset C u v₂ v₃ ).mpr h ) ( ( mem_branchFinset C u v₃ v₃ ).mpr Relation.ReflTransGen.refl );
      · exact fun h => Finset.disjoint_left.mp hd13 ( ( mem_branchFinset C u v₁ v₃ ).mpr h ) ( ( mem_branchFinset C u v₃ v₃ ).mpr Relation.ReflTransGen.refl );
      · exact fun h => Finset.disjoint_left.mp hd23 ( ( mem_branchFinset C u v₂ v₂ ).mpr Relation.ReflTransGen.refl ) ( ( mem_branchFinset C u v₃ v₂ ).mpr h );
      · exact fun h => Finset.disjoint_left.mp hd12 ( ( mem_branchFinset C u v₁ v₂ ).mpr h ) ( ( mem_branchFinset C u v₂ v₂ ).mpr Relation.ReflTransGen.refl );
      · exact fun h => Finset.disjoint_left.mp hd13 ( ( mem_branchFinset C u v₁ v₁ ).mpr Relation.ReflTransGen.refl ) ( ( mem_branchFinset C u v₃ v₁ ).mpr h );
      · exact fun h => Finset.disjoint_left.mp hd12 ( ( mem_branchFinset C u v₁ v₁ ).mpr Relation.ReflTransGen.refl ) ( ( mem_branchFinset C u v₂ v₁ ).mpr h );
    · simp +contextual [ ← htrip, neighbor_iff_Gadj ];
    · grind +suggestions;
  rw [ ← h_split, ‹ ( ∑ i : Fin n, ∑ j : Fin n, if Gadj C i j then ( if i = u then 1 else y₁ i + y₂ i + y₃ i ) * if j = u then 1 else y₁ j + y₂ j + y₃ j else 0 ) = _› ];
  congr! 2;
  · congr! 1;
    · rw [ ← Finset.sum_subset ( show branchFinset C u v₁ ⊆ Finset.univ.erase u from fun x hx => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hu1 hx ) ( Finset.mem_univ x ) ) ];
      · refine' Finset.sum_congr rfl fun i hi => _;
        rw [ ← Finset.sum_subset ( show branchFinset C u v₁ ⊆ Finset.univ.erase u from fun x hx => Finset.mem_erase_of_ne_of_mem ( by
                                    exact fun h => hu1 <| h ▸ hx ) ( Finset.mem_univ x ) ) ];
        grind;
      · simp +contextual [ hs1 ];
    · rw [ ← Finset.sum_subset ( show branchFinset C u v₂ ⊆ Finset.univ.erase u from ?_ ) ];
      · refine' Finset.sum_congr rfl fun i hi => _;
        rw [ ← Finset.sum_subset ( show branchFinset C u v₂ ⊆ Finset.univ.erase u from fun x hx => Finset.mem_erase_of_ne_of_mem ( by
                                    exact fun h => hu2 <| h ▸ hx ) ( Finset.mem_univ x ) ) ];
        grind +suggestions;
      · simp +contextual [ hs2 ];
      · exact fun x hx => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hu2 hx ) ( Finset.mem_univ x );
  · rw [ ← Finset.sum_subset ( show branchFinset C u v₃ ⊆ Finset.univ.erase u from ?_ ) ];
    · refine' Finset.sum_congr rfl fun i hi => _;
      rw [ ← Finset.sum_subset ( show branchFinset C u v₃ ⊆ Finset.univ.erase u from ?_ ) ];
      · grind;
      · exact fun x hx => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hu3 hx ) ( Finset.mem_univ x );
    · simp +contextual [ hs3 ];
    · exact fun x hx => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hu3 hx ) ( Finset.mem_univ x )

/-- **Distinctness of branches.**  At a degree-3 vertex of a positive-definite
Dynkin graph, the three branches are pairwise disjoint (otherwise there is a cycle
through `u`, whose all-ones vector violates positive-definiteness). -/
lemma branches_disjoint (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (hP : (SymmMatrix C).PosDef) (u : Fin n) (v v' : Fin n) (hvv : v ≠ v')
    (hv : v ∈ neighborSet C u) (hv' : v' ∈ neighborSet C u) :
    Disjoint (branchFinset C u v) (branchFinset C u v') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  have hvu : v ≠ u := ((neighbor_iff_Gadj C u v).mp hv).1.symm
  have hadjsymm : Symmetric (adjExcl C u) := by
    rintro a b ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3, h2, fun h => h4 ((hGCM.vanish_symm b a).mp h)⟩
  have hreach_w : reachExcl C u v w := (mem_branchFinset C u v w).mp hw
  have hreach_w' : reachExcl C u v' w := (mem_branchFinset C u v' w).mp hw'
  have hv'B : v' ∈ branchFinset C u v :=
    (mem_branchFinset C u v v').mpr (hreach_w.trans (Relation.ReflTransGen.symmetric hadjsymm hreach_w'))
  have hvB : v ∈ branchFinset C u v := (mem_branchFinset C u v v).mpr Relation.ReflTransGen.refl
  have huB : u ∉ branchFinset C u v := u_notMem_branch C u v hvu
  have hGuv : Gadj C u v := (neighbor_iff_Gadj C u v).mp hv
  have hGuv' : Gadj C u v' := (neighbor_iff_Gadj C u v').mp hv'
  have hEB := connected_edge_bound (Gadj C) (Gadj_symm C hGCM) (Gadj_irr C)
    (branchFinset C u v) v hvB (branch_connected C u v)
  have hDu : (2:ℝ) ≤ ∑ j ∈ branchFinset C u v, (if Gadj C u j then (1:ℝ) else 0) := by
    have hsubset : ({v, v'} : Finset (Fin n)) ⊆ branchFinset C u v := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvB
      · exact hv'B
    calc (2:ℝ) = ∑ j ∈ ({v, v'} : Finset (Fin n)), (if Gadj C u j then (1:ℝ) else 0) := by
            rw [Finset.sum_pair hvv, if_pos hGuv, if_pos hGuv']; norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
  have hxnn : ∀ i, 0 ≤ (fun i => if i ∈ insert u (branchFinset C u v) then (1:ℝ) else 0) i := by
    intro i; dsimp only; split_ifs <;> norm_num
  have hxne : (fun i => if i ∈ insert u (branchFinset C u v) then (1:ℝ) else 0) ≠ 0 := by
    intro h
    have h0 : (fun i => if i ∈ insert u (branchFinset C u v) then (1:ℝ) else 0) u = 0 := by
      rw [h]; rfl
    simp only [Finset.mem_insert, true_or, if_true] at h0
    exact one_ne_zero h0
  have hpos := hP.dotProduct_mulVec_pos hxne
  have hle := form_le_Gadj C hGCM
    (fun i => if i ∈ insert u (branchFinset C u v) then (1:ℝ) else 0) hxnn
  simp only at hle
  rw [indicator_sq_sum, indicator_cross_sum,
    insert_root_edge_sum (Gadj C) (Gadj_symm C hGCM) (Gadj_irr C) (branchFinset C u v) u huB,
    Finset.card_insert_of_notMem huB] at hle
  push_cast at hle
  nlinarith [hpos, hle, hEB, hDu]

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
  obtain ⟨y₁, hy₁nn, hy₁s, hy₁E⟩ := branch_marking C hGCM u v₁
  obtain ⟨y₂, hy₂nn, hy₂s, hy₂E⟩ := branch_marking C hGCM u v₂
  obtain ⟨y₃, hy₃nn, hy₃s, hy₃E⟩ := branch_marking C hGCM u v₃
  have hd12 := branches_disjoint C hGCM hP u v₁ v₂ hdist.1 hv₁ hv₂
  have hd13 := branches_disjoint C hGCM hP u v₁ v₃ hdist.2.1 hv₁ hv₃
  have hd23 := branches_disjoint C hGCM hP u v₂ v₃ hdist.2.2 hv₂ hv₃
  have hxnn : ∀ i, 0 ≤ (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) i := by
    intro i; simp only; split_ifs
    · norm_num
    · exact add_nonneg (add_nonneg (hy₁nn i) (hy₂nn i)) (hy₃nn i)
  have hxne : (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) ≠ 0 := by
    intro h
    have : (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) u = 0 := by rw [h]; rfl
    simp at this
  have hpos := hP.dotProduct_mulVec_pos hxne
  have hle := form_le_Gadj C hGCM (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) hxnn
  have hsq := assembly_sq C u v₁ v₂ v₃ y₁ y₂ y₃ hu1 hu2 hu3 hy₁s hy₂s hy₃s hd12 hd13 hd23
  have hcr := assembly_cross C hGCM u v₁ v₂ v₃ y₁ y₂ y₃ htrip hu1 hu2 hu3 hy₁s hy₂s hy₃s
    hd12 hd13 hd23
  simp only at hle
  rw [hsq, hcr] at hle
  linarith [hpos, hle, hy₁E, hy₂E, hy₃E, hcon]

theorem branciSize_inequality (C : Matrix (Fin n) (Fin n) ℤ)
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
