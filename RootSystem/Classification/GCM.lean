import Mathlib.Data.Matrix.Cartan
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic
import RootSystem.SymmMatrix.Basic

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
    dsimp [reindex_apply, submatrix_apply]
    exact hC.off_diag_nonpos _ _ (fun h => hij (σ.symm.injective (by simp [h])))
  · intro i j
    dsimp [reindex_apply, submatrix_apply]
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
    simp at hTuniv
    contradiction
  have hTne : σ ⁻¹' S ≠ ∅ := by
    intro hTempty
    rw [Set.preimage_eq_empty_iff] at hTempty
    simp at hTempty
    contradiction
  rcases hC (σ ⁻¹' S) hTne hT with ⟨i, hiT, j, hjT, hij⟩
  use σ i, hiT, σ j, by
    simp at hjT
    simp [hjT]
  simp at hij
  simpa

variable {n : ℕ}

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

/-
If C i j ≠ 0 and i ≠ j in a GCM, then SymmMatrix C i j ≤ -1.
-/
lemma symmMatrix_adj_le_neg_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    {i j : Fin n} (hij : i ≠ j) (hadj : C i j ≠ 0) :
    SymmMatrix C i j ≤ -1 := by
  have := edge_product_ge_one C hGCM i j hij hadj
  -- Since $C i j \neq 0$ and $C i j \leq 0$, we have $C i j \leq -1$. By $hsym$, $C j i \neq 0$, and similarly $C j i \leq -1$. So $C i j * C j i = |C i j| * |C j i| \geq 1 * 1 = 1$.
  unfold SymmMatrix
  simp [hij]
  exact_mod_cast this

/-! ### The root system Cartan matrix is a generalized Cartan matrix

This shows that the Cartan matrix coming from a root system satisfies the abstract
axioms, connecting the root system classification to the Cartan matrix classification. -/

variable {ι E F : Type*} [Finite ι]
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (P : RootPairing ι ℝ E F) [P.IsCrystallographic] (b : P.Base)

/-- The Cartan matrix of a crystallographic root system is a generalized Cartan matrix. -/
theorem rootSystem_isGCM [DecidableEq b.support] :
    IsGeneralizedCartanMatrix b.cartanMatrix := by
  constructor
  · intro i; exact b.cartanMatrix_apply_same i
  · intro i j hij
    have h := b.cartanMatrix_mem_of_ne hij
    simp at h; omega
  · intro i j; exact b.cartanMatrix_apply_eq_zero_iff_symm
