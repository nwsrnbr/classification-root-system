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
