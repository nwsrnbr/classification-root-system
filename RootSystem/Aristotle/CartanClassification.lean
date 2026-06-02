import Mathlib

/-!
# Classification of Irreducible Crystallographic Root Systems via Cartan Matrices

## Cartan matrices and Coxeter–Dynkin diagrams

There is a bijective correspondence between:
- Cartan matrices (up to simultaneous row/column permutation), and
- Coxeter–Dynkin diagrams (up to graph isomorphism).

Given a Cartan matrix `C` indexed by a set `I`:
- The **vertices** of the Dynkin diagram are the elements of `I`.
- There is an **edge** between `i` and `j` iff `C i j * C j i ≠ 0`.
- The **edge multiplicity** is `C i j * C j i ∈ {1, 2, 3}`.
- The **arrow** points from `i` to `j` when `|C i j| > |C j i|` (i.e., toward the shorter root).

## The indexing issue

The Cartan matrix `C` depends on the choice of labeling (indexing) of the simple roots.
If we relabel using a bijection `σ : I ≃ J`, we get a new matrix `C' = C.reindex σ σ`,
where `C' (σ i) (σ j) = C i j`. This is exactly simultaneous permutation of rows and columns.

**This is not the main difficulty** of the classification. Rather, it is a standard and
well-understood equivalence relation. The `reindex` in the classification statement
simply says "up to relabeling of simple roots." The **hard part** is the combinatorial
case analysis showing that only finitely many Dynkin diagram shapes are possible.

## Classification in terms of Cartan matrices

The classification can indeed be stated purely in terms of Cartan matrices, without
any reference to root systems or Lie algebras. We define:
- `IsGeneralizedCartanMatrix C`: the matrix has 2's on the diagonal, non-positive
  off-diagonal integer entries, and `C i j = 0 ↔ C j i = 0`.
- `IsIndecomposable C`: the matrix cannot be written as a block-diagonal matrix
  (equivalently, its Dynkin diagram is connected).
- `IsFiniteType C`: the symmetrized matrix is positive definite
  (equivalently, the associated Kac–Moody algebra is finite-dimensional).

The classification theorem then states: every indecomposable generalized Cartan matrix
of finite type is equivalent (via reindexing) to exactly one of
`A n`, `B n`, `C n`, `D n`, `E₆`, `E₇`, `E₈`, `F₄`, `G₂`.

## Relationship to the root system classification

The classification of irreducible crystallographic root systems follows because:
1. Every such root system determines a Cartan matrix (from its base/simple roots).
2. The Cartan matrix is a generalized Cartan matrix of finite type.
3. The Cartan matrix determines the root system up to isomorphism.
4. The Cartan matrix classification gives the result.
-/

namespace CartanClassification

open Matrix CartanMatrix

/-! ### Abstract Cartan matrices -/

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

/-- Two matrices are **Cartan-equivalent** if they are related by simultaneous
  permutation of rows and columns (i.e., reindexing).
  Here `σ : m ≃ n` gives `(reindex σ σ) C` with `((reindex σ σ) C) i j = C (σ⁻¹ i) (σ⁻¹ j)`. -/
def CartanEquiv {m n : Type} (C : Matrix m m ℤ) (C' : Matrix n n ℤ) : Prop :=
  ∃ σ : m ≃ n, C' = (Matrix.reindex σ σ) C

/-! ### Properties of Cartan equivalence -/

/-- Cartan equivalence is reflexive. -/
theorem CartanEquiv.refl {n : Type} (C : Matrix n n ℤ) : CartanEquiv C C := by
  exact ⟨Equiv.refl n, by ext; simp [reindex_apply, submatrix_apply]⟩

/-- Cartan equivalence is symmetric. -/
theorem CartanEquiv.symm {m n : Type} {C : Matrix m m ℤ} {C' : Matrix n n ℤ}
    (h : CartanEquiv C C') : CartanEquiv C' C := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.symm, by subst hσ; ext; simp [reindex_apply, submatrix_apply]⟩

/-- Cartan equivalence is transitive. -/
theorem CartanEquiv.trans {l m n : Type}
    {C₁ : Matrix l l ℤ} {C₂ : Matrix m m ℤ} {C₃ : Matrix n n ℤ}
    (h₁ : CartanEquiv C₁ C₂) (h₂ : CartanEquiv C₂ C₃) : CartanEquiv C₁ C₃ := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  exact ⟨σ₁.trans σ₂, by subst hσ₁ hσ₂; ext; simp [reindex_apply, submatrix_apply]⟩

/-- Cartan equivalence preserves the generalized Cartan matrix property. -/
theorem IsGeneralizedCartanMatrix.of_cartanEquiv {m n : Type}
    [DecidableEq m] [DecidableEq n]
    {C : Matrix m m ℤ} {C' : Matrix n n ℤ}
    (hC : IsGeneralizedCartanMatrix C) (h : CartanEquiv C C') :
    IsGeneralizedCartanMatrix C' := by
  obtain ⟨σ, hσ⟩ := h
  subst hσ
  constructor
  · intro i; simp [reindex_apply, submatrix_apply, hC.diag]
  · intro i j hij
    simp [reindex_apply, submatrix_apply]
    exact hC.off_diag_nonpos _ _ (fun h => hij (σ.symm.injective (by simp [h])))
  · intro i j
    simp [reindex_apply, submatrix_apply]
    exact hC.vanish_symm _ _

/-
Cartan equivalence preserves indecomposability.
-/
theorem IsIndecomposable.of_cartanEquiv {m n : Type}
    [DecidableEq m] [DecidableEq n]
    {C : Matrix m m ℤ} {C' : Matrix n n ℤ}
    (hC : IsIndecomposable C) (h : CartanEquiv C C') :
    IsIndecomposable C' := by
  -- We have `h : CartanEquiv C C'`, i.e., an equivalence `σ : m ≃ n` such that `C' = (reindex σ σ) C`.
  -- We can extract `σ`, rewrite `C'` as the reindex image, then introduce a subset `S ⊆ n` and use the bijection `σ`
  -- to transport the hypothesis `hC` (indecomposability of `C`) to the required statement for `C'`.
  rcases h with ⟨σ, hσ⟩
  rw [hσ]
  intro S hSne hSneuniv
  have hT : σ ⁻¹' S ≠ Set.univ := by
    intro hTuniv
    rw [Set.preimage_eq_univ_iff] at hTuniv
    simp [funext_iff] at hTuniv
    exact hSneuniv hTuniv
  have hTne : σ ⁻¹' S ≠ ∅ := by
    intro hTempty
    rw [Set.preimage_eq_empty_iff] at hTempty
    simp at hTempty
    exact hSne hTempty
  rcases hC (σ ⁻¹' S) hTne hT with ⟨i, hiT, j, hjT, hij⟩
  use σ i, hiT, σ j, by
    simp at hjT
    simp [hjT]
  simp at hij
  simpa

/-! ### The standard Cartan matrices are generalized Cartan matrices -/

theorem A_isGCM (n : ℕ) : IsGeneralizedCartanMatrix (CartanMatrix.A n) := by
  constructor
  · intro i; simp [CartanMatrix.A]
  · intro i j hij; simp [CartanMatrix.A]; omega
  · intro i j; simp [CartanMatrix.A]; constructor <;> intro h <;> omega

theorem A_isIndecomposable (n : ℕ) (hn : 1 ≤ n) : IsIndecomposable (CartanMatrix.A n) := by
  intro S hS_nonempty hS_ne_univ;
  -- Since S is a proper nonempty subset, there exist i ∈ S and j ∉ S with |i-j| = 1.
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i ∈ S := by
    exact Set.nonempty_iff_ne_empty.2 hS_nonempty
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ S := by
    exact Set.nonempty_compl.2 hS_ne_univ
  have h_adj : ∃ i j : Fin n, i ∈ S ∧ j ∉ S ∧ (i.val - j.val = 1 ∨ j.val - i.val = 1) := by
    induction' i with i ih generalizing j;
    induction' j with j ih'izing i;
    induction' i with i ih generalizing j;
    · induction' j with j ih'izing generalizing S;
      · tauto;
      · grind +splitImp;
    · grind +extAll;
  obtain ⟨ i, j, hi, hj, h | h ⟩ := h_adj <;> use i, hi, j, hj <;> simp_all +decide [ CartanMatrix.A ]; all_goals grind

/-- The symmetrized Cartan matrix: diagonal entries are 2, off-diagonal entries are
`-√(C i j * C j i)`. A generalized Cartan matrix is of **finite type** iff this is
positive definite. -/
noncomputable def SymmMatrix' {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

/-! ### Classification theorem — Cartan matrix version

This is the classification theorem stated purely in terms of Cartan matrices,
without any reference to root systems, Lie algebras, or inner product spaces.

**Theorem.** Every indecomposable generalized Cartan matrix of finite type is
Cartan-equivalent to exactly one of the standard matrices A_n, B_n, C_n, D_n,
E₆, E₇, E₈, F₄, G₂. -/

/-- The classification of indecomposable generalized Cartan matrices of finite type:
every such matrix (with index set `Fin m`) is Cartan-equivalent to one of the standard types. -/
theorem classification_cartan (m : ℕ) (C : Matrix (Fin m) (Fin m) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (hIndec : IsIndecomposable C)
    (hPosDef : (SymmMatrix' C).PosDef) :
    (∃ n, CartanEquiv (CartanMatrix.A n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.B n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.C n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.D n) C) ∨
    CartanEquiv CartanMatrix.E₆ C ∨
    CartanEquiv CartanMatrix.E₇ C ∨
    CartanEquiv CartanMatrix.E₈ C ∨
    CartanEquiv CartanMatrix.F₄ C ∨
    CartanEquiv CartanMatrix.G₂ C := by
  sorry

/-! ### The root system Cartan matrix is a generalized Cartan matrix

This shows that the Cartan matrix coming from a root system satisfies the abstract
axioms, connecting the root system classification to the Cartan matrix classification. -/

variable {ι E F : Type*} [Finite ι]
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (Φ : RootPairing ι ℝ E F) [Φ.IsCrystallographic] (b : Φ.Base)

/-- The Cartan matrix of a crystallographic root system is a generalized Cartan matrix. -/
theorem rootSystem_isGCM [DecidableEq b.support] :
    IsGeneralizedCartanMatrix b.cartanMatrix := by
  constructor
  · intro i; exact b.cartanMatrix_apply_same i
  · intro i j hij
    have h := b.cartanMatrix_mem_of_ne hij
    simp at h; omega
  · intro i j; exact b.cartanMatrix_apply_eq_zero_iff_symm

/-! ### Uniqueness of the classification (non-isomorphism of distinct types)

The classification is not just an existence result — each type appears exactly once.
No two of the standard Cartan matrices are Cartan-equivalent to each other.
This uniqueness follows from basic invariants: rank, number of edges, etc.

For example, A₂ and G₂ both have rank 2, but they are distinguished by the
off-diagonal product: for A₂ it is 1, for G₂ it is 3. -/

/-- The multiset of off-diagonal products `C i j * C j i` (for `i < j`) is an invariant
of Cartan equivalence. This is the key tool for distinguishing types. -/
def offDiagProducts {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : Multiset ℤ :=
  (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).val.map
    (fun p => C p.1 p.2 * C p.2 p.1)

/-
A₂ and G₂ are not Cartan-equivalent (they have different off-diagonal products).
-/
theorem A2_not_equiv_G2 : ¬ CartanEquiv (CartanMatrix.A 2) CartanMatrix.G₂ := by
  rintro ⟨ σ, h ⟩;
  fin_cases σ <;> simp_all +decide

/-
B₂ and G₂ are not Cartan-equivalent.
-/
theorem B2_not_equiv_G2 : ¬ CartanEquiv (CartanMatrix.B 2) CartanMatrix.G₂ := by
  rintro ⟨ σ, hσ ⟩;
  fin_cases σ <;> simp +decide at hσ





def D_rev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))


/-- The Cartan matrix of type \widetilde{D}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o                       o
     \                     /
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /                     \
    o                       o
```
-/
def D_tilda (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n - 2 ∧ j < n - 2 then (D_rev n) (i.castLT (by omega)) (j.castLT (by omega))
    else if i = j then 2
    else if i.val + 1 = n ∧ (j.val + 3 = n ∨ j.val + 2 = n ∨ j.val = n) then -1
    else if j.val + 1 = n ∧ (i.val + 3 = n ∨ i.val + 2 = n ∨ i.val = n) then -1
    else 0

theorem D_tilda_isNotPosDef (n : ℕ) (hn : 5 ≤ n) : ¬(SymmMatrix' (D_tilda n)).PosDef := by
  sorry

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The principal matrix of order n of `Y`. -/
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

theorem sub_of_pos_def (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (h : (SymmMatrix' C).PosDef) :
    (SymmMatrix' (isTopLeftBlock C)).PosDef := by
  sorry

theorem sub_of_pos_def' (C : Matrix (Fin n) (Fin n) ℤ) (h : (SymmMatrix' C).PosDef) :
    (SymmMatrix' (LowerLabel C)).PosDef := by
  sorry

def Adj (C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : Prop :=
  i ≠ j ∧ C i j ≠ 0

def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  ((Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j).card)

def IsBranch (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop :=
  3 ≤ degree C i

instance IsBranch.decidable (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Decidable (IsBranch C i) :=
  inferInstanceAs (Decidable (3 ≤ degree C i))

def NumOfBranch (C : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (Finset.univ.filter (fun i => IsBranch C i)).card

lemma pos_branch_le_three (hn : 5 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix' C).PosDef) :
  NumOfBranch C ≤ 1 := by
    sorry

end CartanClassification
