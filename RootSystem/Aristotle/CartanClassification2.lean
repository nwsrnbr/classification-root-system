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

def numOfBranch (C : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (Finset.univ.filter (fun i => IsBranch C i)).card

/- The original statement below is false without an indecomposability hypothesis.
   Counterexample: the block-diagonal matrix D₄ ⊕ D₄ is an 8×8 GCM with positive
   definite symmetrization and numOfBranch = 2.
   The corrected version adds `IsIndecomposable C`. -/
-- lemma pos_branch_le_three (hn : 5 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
--     (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix' C).PosDef) :
--   numOfBranch C ≤ 1 := by
--     sorry

/-! ### Graph infrastructure for the corrected proof -/

/-- The Dynkin graph of a generalized Cartan matrix: vertices are `Fin n`,
    and `i` is adjacent to `j` iff `C i j ≠ 0` (and `i ≠ j`). -/
def dynkinGraph (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) : SimpleGraph (Fin n) where
  Adj i j := C i j ≠ 0 ∧ i ≠ j
  symm i j h := ⟨fun h_eq => h.1 ((hGCM.vanish_symm j i).mp h_eq), h.2.symm⟩
  loopless := ⟨fun i h => h.2 rfl⟩

/-
An indecomposable GCM has a connected Dynkin graph.
-/
lemma dynkinGraph_preconnected (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C) :
    (dynkinGraph C hGCM).Preconnected := by
  intro u v
  by_contra h_not_reachable
  set S := {w | (dynkinGraph C hGCM).Reachable u w}
  have hS_nonempty : S.Nonempty := by
    exact ⟨ u, SimpleGraph.Reachable.refl _ ⟩
  have hS_univ : S = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro w
    by_contra hw_not_in_S
    have hS_not_univ : S ≠ Set.univ := by
      exact Set.nonempty_compl.1 ⟨ w, hw_not_in_S ⟩
    have hS_not_univ' : ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0 := by
      exact hI S hS_nonempty.ne_empty hS_not_univ |> fun ⟨ i, hi, j, hj, h ⟩ => ⟨ i, hi, j, hj, h ⟩
    obtain ⟨i, hiS, j, hjS, hCij⟩ := hS_not_univ'
    have h_adj : (dynkinGraph C hGCM).Adj i j := by
      exact ⟨ hCij, by rintro rfl; exact hjS <| hiS ⟩
    have h_reachable : (dynkinGraph C hGCM).Reachable u j := by
      exact hiS.trans ( SimpleGraph.Adj.reachable h_adj )
    exact hjS h_reachable
  have h_contra : v ∈ S := by
    exact hS_univ.symm.subset <| Set.mem_univ v
  exact h_not_reachable h_contra

/-
For i ≠ j with C i j ≠ 0 in a GCM, the product C i j * C j i ≥ 1.
-/
lemma edge_product_ge_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (i j : Fin n) (hij : i ≠ j) (h : C i j ≠ 0) :
    1 ≤ C i j * C j i := by
  cases lt_or_gt_of_ne h <;> have := hGCM.off_diag_nonpos i j hij <;> have := hGCM.off_diag_nonpos j i hij.symm <;> simp_all +decide;
  · nlinarith [ show C i j < 0 from by assumption, show C j i < 0 from lt_of_le_of_ne this ( by have := hGCM.vanish_symm i j; aesop ) ];
  · linarith

/-
If vertex `i` has degree ≥ 3 and `w` is one specific neighbor, there exist
    two more distinct neighbors `a`, `b` of `i` with `a ≠ w` and `b ≠ w`.
-/
lemma exist_two_extra_neighbors (C : Matrix (Fin n) (Fin n) ℤ)
    (i w : Fin n) (hdeg : 3 ≤ degree C i) :
    ∃ a b : Fin n, a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ a ≠ i ∧ b ≠ i ∧ C i a ≠ 0 ∧ C i b ≠ 0 := by
  have h_card : ∃ S : Finset (Fin n), S.card ≥ 2 ∧ ∀ j ∈ S, j ≠ w ∧ j ≠ i ∧ C i j ≠ 0 := by
    use Finset.univ.filter (fun j => C i j ≠ 0 ∧ i ≠ j) \ {w};
    simp_all +decide [ Finset.card_sdiff, degree ];
    exact ⟨ Nat.le_sub_of_add_le ( by linarith [ show Finset.card ( { w } ∩ Finset.filter ( fun j => ¬C i j = 0 ∧ ¬i = j ) Finset.univ ) ≤ 1 by exact Finset.card_le_one.mpr ( by aesop ) ] ), by aesop ⟩;
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_card; obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hS₁; use a, b; aesop;

/-
For a GCM and nonneg vector `x`, the quadratic form `xᵀ (SymmMatrix' C) x`
    is bounded above by `∑ i, 2 * (x i)^2 - 2 * ∑ edges, x i * x j`
    (since √(Cᵢⱼ·Cⱼᵢ) ≥ 1 for each edge and all off-diagonal contributions are ≤ 0).
-/
set_option maxHeartbeats 400000 in
lemma symmMatrix_quadform_upper_bound (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx_nn : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n))
    (hE_adj : ∀ p ∈ E, C p.1 p.2 ≠ 0 ∧ p.1 ≠ p.2)
    (hE_nodup : ∀ p ∈ E, (p.2, p.1) ∉ E) :
    dotProduct x ((SymmMatrix' C).mulVec x) ≤
      ∑ i : Fin n, 2 * (x i) ^ 2 - 2 * ∑ p ∈ E, x p.1 * x p.2 := by
  -- Expand the quadratic form using the definition of `SymmMatrix'`.
  have h_expand : dotProduct x (SymmMatrix' C *ᵥ x) = ∑ i, 2 * (x i)^2 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt ((C i j) * (C j i)) * x i * x j := by
    simp +decide [ SymmMatrix', Matrix.mulVec, dotProduct, Finset.sum_ite, Finset.filter_ne ];
    simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq, Finset.sum_mul ] ; ring;
    simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq, hGCM.diag ] ; ring;
    simp +decide [ Finset.sum_filter, sq ];
  -- Since $\sqrt{(C i j) * (C j i)} \geq 1$ for all $i \neq j$ with $C i j \neq 0$, we can bound the sum.
  have h_bound : ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt ((C i j) * (C j i)) * x i * x j ≥ ∑ p ∈ E, Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 + ∑ p ∈ E, Real.sqrt ((C p.2 p.1) * (C p.1 p.2)) * x p.2 * x p.1 := by
    have h_bound : ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt ((C i j) * (C j i)) * x i * x j ≥ ∑ p ∈ Finset.biUnion E (fun p => {(p.1, p.2), (p.2, p.1)}), Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 := by
      have h_bound : ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt ((C i j) * (C j i)) * x i * x j ≥ ∑ p ∈ Finset.filter (fun p => p.1 ≠ p.2) (Finset.univ : Finset (Fin n × Fin n)), Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 := by
        rw [ Finset.sum_sigma' ];
        refine' le_of_eq _;
        refine' Finset.sum_bij ( fun p hp => ⟨ p.1, p.2 ⟩ ) _ _ _ _ <;> simp +decide;
        · exact fun a b hab => Ne.symm hab;
        · tauto;
        · exact fun p hp => ⟨ p.1, p.2, Ne.symm hp, rfl ⟩;
      refine le_trans ?_ h_bound;
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_ <;> simp +contextual [ Finset.subset_iff ];
      · grind +ring;
      · exact fun _ _ _ _ => mul_nonneg ( mul_nonneg ( Real.sqrt_nonneg _ ) ( hx_nn _ ) ) ( hx_nn _ );
    rw [ Finset.sum_biUnion ] at h_bound;
    · convert h_bound using 1;
      rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun p hp => _ ; rw [ Finset.sum_pair ] ; simp +decide [ *, mul_assoc, mul_comm, mul_left_comm ] ;
      grind;
    · intro p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
      grind +splitImp;
  -- Since $\sqrt{(C i j) * (C j i)} \geq 1$ for all $i \neq j$ with $C i j \neq 0$, we can further bound the sum.
  have h_bound' : ∑ p ∈ E, Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 + ∑ p ∈ E, Real.sqrt ((C p.2 p.1) * (C p.1 p.2)) * x p.2 * x p.1 ≥ 2 * ∑ p ∈ E, x p.1 * x p.2 := by
    have h_bound' : ∀ p ∈ E, Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) * x p.1 * x p.2 + Real.sqrt ((C p.2 p.1) * (C p.1 p.2)) * x p.2 * x p.1 ≥ 2 * x p.1 * x p.2 := by
      intros p hp
      have h_sqrt_ge_one : Real.sqrt ((C p.1 p.2) * (C p.2 p.1)) ≥ 1 := by
        exact Real.le_sqrt_of_sq_le ( mod_cast edge_product_ge_one C hGCM p.1 p.2 ( hE_adj p hp |>.2 ) ( hE_adj p hp |>.1 ) );
      norm_num [ mul_comm ] at *;
      nlinarith only [ show 0 ≤ x p.1 * x p.2 by exact mul_nonneg ( hx_nn _ ) ( hx_nn _ ), Real.sqrt_nonneg ( C p.1 p.2 * C p.2 p.1 ), Real.mul_self_sqrt ( show 0 ≤ ( C p.1 p.2 : ℝ ) * C p.2 p.1 by positivity ), h_sqrt_ge_one ];
    simpa only [ ← Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc ] using Finset.sum_le_sum h_bound';
  linarith

set_option maxHeartbeats 400000 in
/-- Per-vertex bound: if for every vertex i with x i > 0, the sum of x-values
    of its neighbors (in the GCM sense) is ≥ 2 * x i, then the quadratic form
    `xᵀ (SymmMatrix' C) x ≤ 0`. -/
lemma quadform_nonpos_of_neighbor_bound (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (x : Fin n → ℝ) (hx_nn : ∀ i, 0 ≤ x i)
    (h_bound : ∀ i, 0 < x i →
      2 * x i ≤ ∑ j ∈ Finset.filter (fun j => C i j ≠ 0 ∧ i ≠ j) Finset.univ, x j) :
    dotProduct x ((SymmMatrix' C).mulVec x) ≤ 0 := by
  -- For each $i$, consider the "row contribution" $f(i) = 2 * (x i)^2 - x i * \sum_{j \neq i} \sqrt{C_{ij} C_{ji}} x_j$.
  have h_row_contribution : ∀ i, 0 < x i → 2 * (x i)^2 - x i * ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), Real.sqrt (C i j * C j i) * x j ≤ 0 := by
    intro i hi_pos
    have h_sum_bound : ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), Real.sqrt (C i j * C j i) * x j ≥ ∑ j ∈ Finset.univ.filter (fun j => C i j ≠ 0 ∧ i ≠ j), x j := by
      have h_sum_bound : ∀ j ∈ Finset.univ.filter (fun j => C i j ≠ 0 ∧ i ≠ j), Real.sqrt (C i j * C j i) * x j ≥ x j := by
        intros j hj
        have h_sqrt_ge_one : Real.sqrt (C i j * C j i) ≥ 1 := by
          exact Real.le_sqrt_of_sq_le ( mod_cast edge_product_ge_one C hGCM i j ( by aesop ) ( by aesop ) ) ;
        generalize_proofs at *; (
        exact le_mul_of_one_le_left ( hx_nn j ) h_sqrt_ge_one)
      generalize_proofs at *; (
      exact le_trans ( Finset.sum_le_sum h_sum_bound ) ( Finset.sum_le_sum_of_subset_of_nonneg ( fun j hj => by aesop ) fun _ _ _ => mul_nonneg ( Real.sqrt_nonneg _ ) ( hx_nn _ ) ) ;)
    generalize_proofs at *; (
    nlinarith [ h_bound i hi_pos ]);
  -- By definition of SymmMatrix', we can rewrite the dot product as:
  have h_dot_product : x ⬝ᵥ (SymmMatrix' C).mulVec x = ∑ i, x i * (2 * x i - ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), Real.sqrt (C i j * C j i) * x j) := by
    simp +decide [ SymmMatrix', Matrix.mulVec, dotProduct, Finset.sum_ite, Finset.filter_ne' ];
    simp +decide [ Finset.filter_eq, Finset.filter_ne, hGCM.diag ];
    exact Finset.sum_congr rfl fun _ _ => by ring;
  exact h_dot_product ▸ Finset.sum_nonpos fun i _ => if hi : 0 < x i then by linarith [ h_row_contribution i hi ] else by nlinarith [ hx_nn i, show ∑ j with j ≠ i, Real.sqrt ( C i j * C j i ) * x j ≥ 0 from Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.sqrt_nonneg _ ) ( hx_nn _ ) ] ;

set_option maxHeartbeats 800000 in
/-- For a GCM with positive-definite symmetrization, if there exist two branch
    vertices u ≠ v (each of degree ≥ 3), then there is a nonzero nonneg vector
    `x` with `xᵀ (SymmMatrix' C) x ≤ 0`, contradicting positive definiteness.
    The vector assigns 2 to each vertex on a path from u to v,
    and 1 to the extra neighbors of u and v. -/
lemma not_posDef_of_two_branches (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C)
    (u v : Fin n) (huv : u ≠ v)
    (hu_branch : 3 ≤ degree C u) (hv_branch : 3 ≤ degree C v) :
    ¬(SymmMatrix' C).PosDef := by
  intro hPD
  -- Step 1: Get a path from u to v
  have hr : (dynkinGraph C hGCM).Reachable u v := dynkinGraph_preconnected C hGCM hI u v
  obtain ⟨walk⟩ := hr
  let path := walk.toPath
  have hpath_isPath : path.val.IsPath := path.property
  -- The path has length ≥ 1 since u ≠ v
  have hlen : 1 ≤ path.val.length := by
    by_contra h; push_neg at h
    have h0 : path.val.length = 0 := Nat.lt_one_iff.mp h
    exact huv (SimpleGraph.Walk.Nil.eq (SimpleGraph.Walk.nil_iff_length_eq.mpr h0))
  -- Step 2: Get the second vertex of the path and extra neighbors of u
  let w₁ := path.val.getVert 1
  have hadj_u_w1 : (dynkinGraph C hGCM).Adj u w₁ := by
    have := path.val.adj_getVert_succ (by omega : 0 < path.val.length)
    rwa [path.val.getVert_zero] at this
  obtain ⟨a₁, a₂, ha_ne, ha1_ne_w1, ha2_ne_w1, ha1_ne_u, ha2_ne_u, hCa1, hCa2⟩ :=
    exist_two_extra_neighbors C u w₁ hu_branch
  -- Step 3: Get the second-to-last vertex and extra neighbors of v
  let w₂ := path.val.getVert (path.val.length - 1)
  have hadj_w2_v : (dynkinGraph C hGCM).Adj w₂ v := by
    have h := path.val.adj_getVert_succ (show path.val.length - 1 < path.val.length by omega)
    rw [Nat.sub_one_add_one_eq_of_pos (by omega), path.val.getVert_length] at h; exact h
  obtain ⟨b₁, b₂, hb_ne, hb1_ne_w2, hb2_ne_w2, hb1_ne_v, hb2_ne_v, hCb1, hCb2⟩ :=
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
  have h_neighbor_bound : ∀ i, 0 < x i →
      2 * x i ≤ ∑ j ∈ Finset.filter (fun j => C i j ≠ 0 ∧ i ≠ j) Finset.univ, x j := by
    intro i hxi
    -- x i > 0 means i is on the path (x i = 2) or i is an extra (x i = 1)
    simp only [x] at hxi ⊢
    split_ifs at hxi with h_path h_extra
    · -- i is on the path: x i = 2, need ∑ neighbors ≥ 4
      by_cases hi : i = u ∨ i = v;
      · rcases hi with ( rfl | rfl ) <;> simp_all +decide [ Finset.sum_add_distrib ];
        · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
          any_goals exact { w₁, a₁, a₂ };
          · rw [ Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ * ];
            · split_ifs <;> norm_num;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
            · exact ⟨ Ne.symm ha1_ne_w1, Ne.symm ha2_ne_w1 ⟩;
          · simp_all +decide [ Finset.subset_iff, dynkinGraph ];
            grind;
          · exact fun _ _ _ => hx_nn _;
        · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
          rotate_left;
          exact { w₂, b₁, b₂ };
          · grind +locals;
          · exact fun _ _ _ => hx_nn _;
          · rw [ Finset.sum_insert, Finset.sum_insert ] <;> simp_all +decide [ Finset.sum_singleton ];
            · split_ifs <;> norm_num;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
              · simp +zetaDelta at *;
            · tauto;
      · -- Since $i$ is not $u$ or $v$, it must be an interior vertex of the path.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < k ∧ k < path.val.length ∧ path.val.getVert k = i := by
          have h_interior : ∃ k : ℕ, k < path.val.length ∧ path.val.getVert k = i := by
            simp +zetaDelta at *;
            rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at h_path;
            obtain ⟨ k, hk₁, hk₂ ⟩ := h_path;
            refine' ⟨ k, lt_of_le_of_ne hk₂ _, hk₁ ⟩;
            rintro rfl; simp_all +decide
          obtain ⟨ k, hk₁, hk₂ ⟩ := h_interior; use k; rcases k with ( _ | k ) <;> simp_all +decide ;
        -- Since $i$ is an interior vertex, it has at least two neighbors on the path.
        have h_neighbors : (path.val.getVert (k - 1)) ∈ pathVerts ∧ (path.val.getVert (k + 1)) ∈ pathVerts ∧ (path.val.getVert (k - 1)) ≠ i ∧ (path.val.getVert (k + 1)) ≠ i ∧ C i (path.val.getVert (k - 1)) ≠ 0 ∧ C i (path.val.getVert (k + 1)) ≠ 0 := by
          have h_neighbors : (path.val.getVert (k - 1)) ∈ pathVerts ∧ (path.val.getVert (k + 1)) ∈ pathVerts ∧ (path.val.getVert (k - 1)) ≠ i ∧ (path.val.getVert (k + 1)) ≠ i := by
            have h_neighbors : (path.val.getVert (k - 1)) ∈ pathVerts ∧ (path.val.getVert (k + 1)) ∈ pathVerts := by
              simp +zetaDelta at *;
            have h_neighbors : ∀ i j : ℕ, i < j → j ≤ path.val.length → path.val.getVert i ≠ path.val.getVert j := by
              intros i j hij hjl;
              have := hpath_isPath.getVert_injOn;
              exact this.ne ( show i ≤ ( path : SimpleGraph.Walk ( dynkinGraph C hGCM ) u v ).length from by linarith ) ( show j ≤ ( path : SimpleGraph.Walk ( dynkinGraph C hGCM ) u v ).length from by linarith ) ( by linarith );
            grind +qlia;
          have h_neighbors : (dynkinGraph C hGCM).Adj (path.val.getVert k) (path.val.getVert (k - 1)) ∧ (dynkinGraph C hGCM).Adj (path.val.getVert k) (path.val.getVert (k + 1)) := by
            constructor;
            · have := path.val.adj_getVert_succ ( show k - 1 < path.val.length from by omega ) ; simp_all +decide [ SimpleGraph.Walk.adj_getVert_succ ] ;
              convert this.symm using 1 ; rw [ Nat.sub_add_cancel hk.1 ] ; aesop ( simp_config := { singlePass := true } ) ;
            · convert SimpleGraph.Walk.adj_getVert_succ _ _;
              linarith;
          simp_all +decide [ dynkinGraph ];
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        any_goals exact { ( path.val.getVert ( k - 1 ) ), ( path.val.getVert ( k + 1 ) ) };
        · rw [ Finset.sum_pair ] <;> norm_num [ h_neighbors ];
          · split_ifs ; norm_num;
          · intro h; have := hpath_isPath.getVert_injOn; simp_all +decide [ Set.InjOn ] ;
            exact absurd ( this ( show k - 1 ≤ ( path : SimpleGraph.Walk ( dynkinGraph C hGCM ) u v ).length from Nat.sub_le_of_le_add <| by linarith ) ( show k + 1 ≤ ( path : SimpleGraph.Walk ( dynkinGraph C hGCM ) u v ).length from by linarith ) h ) ( by omega );
        · grind;
        · exact fun _ _ _ => hx_nn _
    · -- i is an extra neighbor: x i = 1, need ∑ neighbors ≥ 2
      rcases h_extra with ( rfl | rfl | rfl | rfl );
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show u ∈ _ from _ ) ) <;> simp_all +decide [ dynkinGraph ];
        · simp +zetaDelta at *;
        · split_ifs <;> norm_num;
        · grind +revert;
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show u ∈ _ from _ ) ) <;> simp_all +decide [ dynkinGraph ];
        · exact if_pos ( by exact List.mem_toFinset.mpr <| by simp ) |> fun h => h.symm ▸ by norm_num;
        · split_ifs <;> norm_num;
        · exact fun h => hCa2 <| by simpa [ h ] using hGCM.vanish_symm i u |>.1 h;
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => by positivity ) ( show v ∈ _ from _ ) ) <;> simp +decide [ * ];
        · simp +zetaDelta at *;
        · exact fun h => hCb1 <| by simpa [ h ] using hGCM.vanish_symm i v |>.1 h;
      · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show v ∈ _ from _ ) ) <;> simp_all +decide [ dynkinGraph ];
        · -- Since $v$ is in the pathVerts, the if statement evaluates to 2.
          simp [pathVerts, hlen];
        · split_ifs <;> norm_num;
        · exact fun h => hCb2 <| by simpa [ h ] using hGCM.vanish_symm i v |>.1 h;
    · -- x i = 0, contradiction
      linarith
  -- Step 7: Apply quadform_nonpos_of_neighbor_bound
  have h_le := quadform_nonpos_of_neighbor_bound C hGCM x hx_nn h_neighbor_bound
  -- This contradicts positive definiteness
  have h_pos := hPD.dotProduct_mulVec_pos hx_ne
  simp [star] at h_pos
  linarith

/-! ### The corrected statement and proof -/

/-
**Corrected statement**: An indecomposable GCM of size ≥ 5 with positive-definite
    symmetrization has at most one branch vertex (vertex of degree ≥ 3).
    The proof uses the fact that if there were two branch vertices, we could
    construct a non-negative nonzero vector making the quadratic form ≤ 0,
    contradicting positive definiteness.
-/
lemma pos_numOfBranch_le_one (hn : 5 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C)
    (hP : (SymmMatrix' C).PosDef) :
    numOfBranch C ≤ 1 := by
  contrapose! hP;
  obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp hP;
  exact not_posDef_of_two_branches C hGCM hI u v huv ( by simpa using hu ) ( by simpa using hv )



lemma pos_degree_le_three (hn : 5 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C)
    (hP : (SymmMatrix' C).PosDef) :
    ∀ i, degree C i ≤ 3 := by
  sorry

end CartanClassification
