import Mathlib

namespace CartanMatrix

open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The matrix obtained by replacing each index `i` with `n - i + 1`. -/
def rev (X : Matrix (Fin n) (Fin n) R) := Matrix.of fun i j : Fin n ↦ X (i.rev) (j.rev)

def D_rev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

lemma D_rev_eq (n : ℕ) : D_rev n = rev (D n) := by
  ext i j
  simp [D_rev, rev, D, Fin.rev]
  split_ifs
  <;> grind



variable (n : ℕ)

def A_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (i.val = 0 ∧ j.val = n) ∨ (j.val = 0 ∧ i.val = n) ∨
            (i.val = n - 1 ∧ j.val = n) ∨ (j.val = n - 1 ∧ i.val = n) then -1
    else 0

def B_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (D_rev n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then -1
    else if (i : ℕ) + 1 = j then -2
    else 0

def C_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (rev (C n)) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then -2
    else if (i : ℕ) + 1 = j then -1
    else 0

def D_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n - 2 ∧ j < n - 2 then (D_rev n) (i.castLT (by omega)) (j.castLT (by omega))
    else if i = j then 2
    else if i.val + 1 = n ∧ (j.val + 3 = n ∨ j.val + 2 = n ∨ j.val = n) then -1
    else if j.val + 1 = n ∧ (i.val + 3 = n ∨ i.val + 2 = n ∨ i.val = n) then -1
    else 0

def E_tilda₆ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, -1, 0, 0;
    0, 0, 2, -1, 0, 0, 0;
    0, 0, -1, 2, -1, 0, 0;
    0, -1, 0, -1, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]

def E_tilda₇ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, 0;
    0, 0, -1, 2, -1, -1, 0, 0;
    0, 0, 0, -1, 2, 0, -1, 0;
    0, 0, 0, -1, 0, 2, 0, 0;
    0, 0, 0, 0, -1, 0, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]

def E_tilda₈ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0,  0, -1,  2]

def F_tilda₄ : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1, 0, 0, 0;
    -1, 2, -2, 0, 0;
    0, -1, 2, -1, 0;
    0, 0, -1, 2, -1;
    0, 0, 0, -1, 2]

def G_tilda₂ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -3, 0;
    -1, 2, -1;
    0, -1, 2]



variable {n : ℕ} {k : ℕ} {hk : k ≤ n}

noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)



theorem A_isPosDef (n : ℕ) : (SymmMatrix (A n)).PosDef := by sorry
theorem B_isPosDef (n : ℕ) : (SymmMatrix (B n)).PosDef := by sorry
theorem C_isPosDef (n : ℕ) : (SymmMatrix (C n)).PosDef := by sorry
theorem D_isPosDef (n : ℕ) : (SymmMatrix (D n)).PosDef := by sorry
theorem E₆_isPosDef : (SymmMatrix E₆).PosDef := by sorry
theorem E₇_isPosDef : (SymmMatrix E₇).PosDef := by sorry
theorem E₈_isPosDef : (SymmMatrix E₈).PosDef := by sorry
theorem F₄_isPosDef : (SymmMatrix F₄).PosDef := by sorry
theorem G₂_isPosDef : (SymmMatrix G₂).PosDef := by sorry

theorem B_tilda_isNotPosDef (n : ℕ) (hn : 3 ≤ n) : ¬(SymmMatrix (B_tilda n)).PosDef := by sorry
theorem C_tilda_isNotPosDef (n : ℕ) (hn : 2 ≤ n) : ¬(SymmMatrix (C_tilda n)).PosDef := by sorry
theorem D_tilda_isNotPosDef (n : ℕ) (hn : 5 ≤ n) : ¬(SymmMatrix (D_tilda n)).PosDef := by sorry
theorem E_tilda₆_isNotPosDef : ¬(SymmMatrix E_tilda₆).PosDef := by sorry
theorem E_tilda₇_isNotPosDef : ¬(SymmMatrix E_tilda₇).PosDef := by sorry
theorem E_tilda₈_isNotPosDef : ¬(SymmMatrix E_tilda₈).PosDef := by sorry
theorem F_tilda₄_isNotPosDef : ¬(SymmMatrix F_tilda₄).PosDef := by sorry
theorem G_tilda₂_isNotPosDef : ¬(SymmMatrix G_tilda₂).PosDef := by sorry



variable {ι E F : Type*} [Nonempty ι] [Finite ι] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (Φ : RootPairing ι ℝ E F) [Φ.IsCrystallographic] {b : Φ.Base} (h_irred : Φ.IsIrreducible)

include h_irred in
lemma isPosDef :
    let n := Fintype.card b.support
    let e : b.support ≃ Fin n := Fintype.equivFin _
    (SymmMatrix (b.cartanMatrix.reindex e e)).PosDef := by
  sorry



def isTopLeftBlock (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  Y.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

def LowerLabel (C : Matrix (Fin n) (Fin n) ℤ) :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else
      match C i j with
      | -1 => -1
      | -2 => -1
      | -3 => -2
      | _ => 0

theorem sub_of_pos_def (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (isTopLeftBlock C)).PosDef := by
  sorry

theorem sub_of_pos_def' (C : Matrix (Fin n) (Fin n) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (LowerLabel C)).PosDef := by
  sorry

/-! ## Degree bound -/

/-- The degree of vertex `i` in the Dynkin diagram of `C`: the number of `j ≠ i` with `C i j ≠ 0`. -/
def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j).card

/-
Off-diagonal entries of SymmMatrix are non-positive.
-/
lemma symmMatrix_off_diag_nonpos (C : Matrix (Fin n) (Fin n) ℤ)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    {i j : Fin n} (hij : i ≠ j) :
    SymmMatrix C i j ≤ 0 := by
  unfold SymmMatrix;
  simp +decide [ hij, hoff, hsym ]

/-
If C i j ≠ 0 and i ≠ j in a GCM, then SymmMatrix C i j ≤ -1.
-/
lemma symmMatrix_adj_le_neg_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    {i j : Fin n} (hij : i ≠ j) (hadj : C i j ≠ 0) :
    SymmMatrix C i j ≤ -1 := by
  -- Since $C i j \neq 0$ and $C i j \leq 0$, we have $C i j \leq -1$. By $hsym$, $C j i \neq 0$, and similarly $C j i \leq -1$. So $C i j * C j i = |C i j| * |C j i| \geq 1 * 1 = 1$.
  have h_prod : C i j * C j i ≥ 1 := by
    cases lt_or_gt_of_ne hadj <;> nlinarith [ hoff i j hij, hoff j i ( Ne.symm hij ), show C j i < 0 from lt_of_le_of_ne ( hoff j i ( Ne.symm hij ) ) ( by specialize hsym i j; aesop ) ];
  unfold SymmMatrix;
  simp +decide [ hij, hadj, h_prod ];
  exact_mod_cast h_prod

/-
In a generalized Cartan matrix with positive definite symmetrization,
every vertex has degree at most 3.
-/
lemma pos_degree_le_three (C : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : ∀ i, C i i = 2)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    (hP : (SymmMatrix C).PosDef) (i : Fin n) :
    degree C i ≤ 3 := by
  by_contra h_deg_ge_4;
  obtain ⟨N, hN⟩ : ∃ N : Finset (Fin n), N.card ≥ 4 ∧ ∀ j ∈ N, C i j ≠ 0 ∧ i ≠ j := by
    exact ⟨ _, not_le.mp h_deg_ge_4, fun j hj => by simpa using hj ⟩;
  -- Construct the vector x : Fin n → ℝ with x i = 2 and x j = 1 for j ∈ N, and x j = 0 otherwise.
  set x : Fin n → ℝ := fun j => if j = i then 2 else if j ∈ N then 1 else 0;
  -- Compute x^T (SymmMatrix C) x.
  have h_x_transpose_SymmMatrix_x : ∑ a, ∑ b, x a * (SymmMatrix C) a b * x b ≤ 8 - 2 * N.card := by
    have h_x_transpose_SymmMatrix_x : ∑ a, ∑ b, x a * (SymmMatrix C) a b * x b = 8 + ∑ a ∈ N, ∑ b ∈ N, (SymmMatrix C) a b + ∑ a ∈ N, (SymmMatrix C) i a * 2 + ∑ a ∈ N, (SymmMatrix C) a i * 2 := by
      simp +zetaDelta at *;
      simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', Finset.sum_add_distrib];
      by_cases hi : i ∈ N <;> simp_all +decide ; ring;
      · exact absurd ( hN.2 i hi ) ( by tauto );
      · unfold SymmMatrix; norm_num [ hdiag ] ; ring;
    -- By symmMatrix_adj_le_neg_one, each SymmMatrix C i b ≤ -1, so the total from these terms (counting both a=i,b∈N and a∈N,b=i) is ≤ -4|N|.
    have h_sum_adj : ∑ a ∈ N, (SymmMatrix C) i a * 2 + ∑ a ∈ N, (SymmMatrix C) a i * 2 ≤ -4 * N.card := by
      have h_sum_adj : ∀ a ∈ N, (SymmMatrix C) i a ≤ -1 ∧ (SymmMatrix C) a i ≤ -1 := by
        intros a ha
        have h_adj : C i a ≠ 0 ∧ C a i ≠ 0 := by
          grind;
        exact ⟨ symmMatrix_adj_le_neg_one C hoff hsym ( hN.2 a ha |>.2 ) h_adj.1, symmMatrix_adj_le_neg_one C hoff hsym ( Ne.symm ( hN.2 a ha |>.2 ) ) h_adj.2 ⟩;
      exact le_trans ( add_le_add ( Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right ( h_sum_adj a ha |>.1 ) zero_le_two ) ( Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right ( h_sum_adj a ha |>.2 ) zero_le_two ) ) ( by norm_num; linarith );
    -- By symmMatrix_off_diag_nonpos, each SymmMatrix C a b ≤ 0 for a ≠ b, so the total from these terms is ≤ 0.
    have h_sum_off_diag : ∑ a ∈ N, ∑ b ∈ N, (SymmMatrix C) a b ≤ 2 * N.card := by
      have h_sum_off_diag : ∑ a ∈ N, ∑ b ∈ N, (SymmMatrix C) a b ≤ ∑ a ∈ N, (SymmMatrix C) a a := by
        have h_sum_off_diag : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → (SymmMatrix C) a b ≤ 0 := by
          exact fun a ha b hb hab => symmMatrix_off_diag_nonpos C hoff hsym hab;
        exact Finset.sum_le_sum fun a ha => by rw [ Finset.sum_eq_add_sum_diff_singleton ha ] ; exact add_le_of_nonpos_right <| Finset.sum_nonpos fun b hb => h_sum_off_diag a ha b ( Finset.mem_sdiff.mp hb |>.1 ) <| by aesop;
      exact h_sum_off_diag.trans ( by rw [ Finset.sum_congr rfl fun _ _ => show SymmMatrix C _ _ = 2 by unfold SymmMatrix; aesop ] ; norm_num; linarith );
    linarith;
  -- Since $x$ is nonzero, we have $x^T (SymmMatrix C) x > 0$.
  have h_x_transpose_SymmMatrix_x_pos : 0 < ∑ a, ∑ b, x a * (SymmMatrix C) a b * x b := by
    have := hP.2;
    convert this ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from ?_ ) using 1;
    · simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
    · simp +zetaDelta at *;
      exact ne_of_apply_ne ( fun f => f i ) ( by norm_num );
  linarith [ show ( N.card : ℝ ) ≥ 4 by norm_cast; linarith ]

/-! ## Helper lemmas for the classification -/

omit [Nonempty ι] [Finite ι] in
lemma classification_rank1
    (h1 : Fintype.card b.support = 1) :
    ∃ (σ : Fin 1 ≃ {x // x ∈ b.support}),
      b.cartanMatrix = ((A 1).reindex σ σ) := by
  obtain ⟨σ, _⟩ : ∃ σ : Fin 1 ≃ b.support, True :=
    ⟨Fintype.equivOfCardEq h1.symm, trivial⟩
  refine ⟨σ, ?_⟩
  ext i j
  obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.mp h1
  simp +decide [hk i, hk j, A]

omit [Nonempty ι] in
lemma cartan_prod_mem
    (i j : b.support) (hij : i ≠ j) :
    b.cartanMatrix i j * b.cartanMatrix j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  have h_mem : b.cartanMatrix i j ∈ ({-3, -2, -1, 0} : Set ℤ) ∧
    b.cartanMatrix j i ∈ ({-3, -2, -1, 0} : Set ℤ) :=
    ⟨b.cartanMatrix_mem_of_ne hij, b.cartanMatrix_mem_of_ne hij.symm⟩
  have h_pairing_mem : (Φ.pairingIn ℤ i j, Φ.pairingIn ℤ j i) ∈
    ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1),
      (-1, -3), (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} :
      Set (ℤ × ℤ)) := by
    convert Φ.pairingIn_pairingIn_mem_set_of_isCrystallographic i j using 1
  simp_all +decide [RootPairing.Base.cartanMatrixIn_def]
  rcases h_pairing_mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    <;> simp_all +decide only
  grind +suggestions

/-! ## The classification theorem

The classification of irreducible crystallographic root systems: any such root system
has a Cartan matrix (with respect to any base) that is isomorphic to one of the standard
types A_n, B_n, C_n, D_n, E₆, E₇, E₈, F₄, or G₂.

The proof follows the standard argument:
1. The symmetrized Cartan matrix is positive definite (isPosDef).
2. Principal submatrices of positive definite matrices are positive definite (sub_of_pos_def).
3. The affine Cartan matrices are NOT positive definite (*_isNotPosDef).
4. Therefore, the Cartan matrix cannot contain any affine Dynkin diagram as a subdiagram.
5. By elimination (extensive case analysis on the graph structure), the only remaining
   possibilities are the standard finite types.
-/

include h_irred in
theorem classification :
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((A n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((B n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((C n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((D n).reindex σ σ)) ∨
  (∃ (σ : Fin 6 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₆).reindex σ σ)) ∨
  (∃ (σ : Fin 7 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₇).reindex σ σ)) ∨
  (∃ (σ : Fin 8 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₈).reindex σ σ)) ∨
  (∃ (σ : Fin 4 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((F₄).reindex σ σ)) ∨
  (∃ (σ : Fin 2 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((G₂).reindex σ σ)) := by
  classical
  let m := Fintype.card b.support
  -- Case split on the rank
  by_cases h1 : m = 1
  · -- Rank 1: this is A₁
    exact Or.inl ⟨1, (classification_rank1 Φ h1).choose, (classification_rank1 Φ h1).choose_spec⟩
  · -- Rank ≥ 2: requires the full Dynkin diagram classification
    -- The proof uses isPosDef, sub_of_pos_def, and *_isNotPosDef to rule out
    -- non-standard configurations by showing they contain affine subdiagrams.
    sorry

end CartanMatrix