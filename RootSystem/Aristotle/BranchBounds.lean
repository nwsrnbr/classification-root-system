import Mathlib

namespace CartanMatrix

open Matrix Finset

variable {n : ℕ}

/-! ## Definitions from test.lean (repeated for self-containment) -/

noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j).card

/-! ## GCM hypotheses bundled -/

/-- Standard GCM hypotheses used throughout. -/
structure IsGCM' (C : Matrix (Fin n) (Fin n) ℤ) : Prop where
  diag : ∀ i, C i i = 2
  off : ∀ i j, i ≠ j → C i j ≤ 0
  sym : ∀ i j, C i j = 0 ↔ C j i = 0

/-! ## Neighbor set -/

/-- The set of neighbors of vertex `u` in the Dynkin diagram. -/
def neighborSet (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => C u j ≠ 0 ∧ u ≠ j

lemma neighborSet_card_eq_degree (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) :
    (neighborSet C u).card = degree C u := rfl

/-! ## Branch definition via reachability -/

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

/-! ## Key lemmas about SymmMatrix entries -/

lemma symmMatrix_off_diag_nonpos' (C : Matrix (Fin n) (Fin n) ℤ)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    {i j : Fin n} (hij : i ≠ j) :
    SymmMatrix C i j ≤ 0 := by
  unfold SymmMatrix; simp +decide [hij, hoff, hsym]

lemma symmMatrix_adj_le_neg_one' (C : Matrix (Fin n) (Fin n) ℤ)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    {i j : Fin n} (hij : i ≠ j) (hadj : C i j ≠ 0) :
    SymmMatrix C i j ≤ -1 := by
  have h_prod : C i j * C j i ≥ 1 := by
    cases lt_or_gt_of_ne hadj <;>
      nlinarith [hoff i j hij, hoff j i (Ne.symm hij),
        show C j i < 0 from lt_of_le_of_ne (hoff j i (Ne.symm hij))
          (by specialize hsym i j; aesop)]
  unfold SymmMatrix; simp +decide [hij, hadj, h_prod]; exact_mod_cast h_prod

/-! ## No-cycle lemma -/

set_option maxHeartbeats 800000 in
/-
A cycle of length ≥ 3 in a GCM with positive definite symmetrization is impossible.
    Here the cycle is given as an injective map `f : Fin k → Fin n` with `f i` adjacent to
    `f (i+1 mod k)` for all `i`.
-/
lemma no_cycle (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (k : ℕ) (hk : 3 ≤ k) (f : Fin k ↪ Fin n)
    (hcycle : ∀ i : Fin k, C (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0) :
    False := by
  -- Define the vector x such that x_i = 1 for all i in the cycle, and x_i = 0 elsewhere.
  set x : Fin n → ℝ := fun i => if ∃ j : Fin k, f j = i then 1 else 0;
  -- By definition of $x$, we have $x^T (SymmMatrix C) x \leq 0$.
  have h_quad_form : ∑ i, ∑ j, x i * (SymmMatrix C) i j * x j ≤ 0 := by
    -- By definition of $x$, we have $x_i = 1$ for all $i$ in the cycle and $x_i = 0$ elsewhere.
    have hx : ∑ i, ∑ j, x i * (SymmMatrix C) i j * x j = ∑ i : Fin k, (SymmMatrix C) (f i) (f i) + ∑ i : Fin k, ∑ j ∈ Finset.univ.erase i, (SymmMatrix C) (f i) (f j) := by
      have hx : ∑ i, ∑ j, x i * (SymmMatrix C) i j * x j = ∑ i ∈ Finset.image f Finset.univ, ∑ j ∈ Finset.image f Finset.univ, (SymmMatrix C) i j := by
        simp +zetaDelta at *;
        simp +decide [ Finset.sum_ite, Finset.filter_image ];
      simp_all +decide [ Finset.sum_image, Function.Injective ];
    -- Since $C$ is a GCM, we know that $C (f i) (f j) \leq 0$ for all $i \neq j$.
    have h_off_diag : ∀ i j : Fin k, i ≠ j → (SymmMatrix C) (f i) (f j) ≤ 0 := by
      intros i j hij
      apply symmMatrix_off_diag_nonpos' C hG.off hG.sym
      simp [hij];
    -- Since $C$ is a GCM, we know that $C (f i) (f (i+1)) \leq -1$ for all $i$.
    have h_adj : ∀ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) ≤ -1 := by
      intros i
      have h_adj_i : C (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) ≠ 0 := hcycle i
      have h_adj_i_le : SymmMatrix C (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) ≤ -1 := by
        apply symmMatrix_adj_le_neg_one' C hG.off hG.sym;
        · simp_all +decide [ Fin.ext_iff, Nat.mod_eq_of_lt ];
          by_contra h_contra;
          have := Nat.mod_add_div ( i + 1 ) k;
          nlinarith [ show ( i : ℕ ) < k from i.2, show ( ( i + 1 ) / k : ℕ ) = 0 from by nlinarith [ show ( i : ℕ ) < k from i.2 ] ];
        · assumption
      exact h_adj_i_le;
    -- Since $C$ is a GCM, we know that $C (f i) (f (i+1)) \leq -1$ for all $i$, and there are $k$ such terms.
    have h_sum_adj : ∑ i : Fin k, ∑ j ∈ Finset.univ.erase i, (SymmMatrix C) (f i) (f j) ≤ ∑ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) + ∑ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩) := by
      have h_sum_adj : ∀ i : Fin k, ∑ j ∈ Finset.univ.erase i, (SymmMatrix C) (f i) (f j) ≤ (SymmMatrix C) (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) + (SymmMatrix C) (f i) (f ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩) := by
        intro i
        have h_sum_adj_i : ∑ j ∈ Finset.univ.erase i \ {⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩, ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩}, (SymmMatrix C) (f i) (f j) ≤ 0 := by
          refine' Finset.sum_nonpos fun j hj => h_off_diag i j _;
          grind;
        rw [ ← Finset.sum_sdiff ( show { ⟨ ( i + 1 ) % k, Nat.mod_lt _ ( by linarith ) ⟩, ⟨ ( i + k - 1 ) % k, Nat.mod_lt _ ( by linarith ) ⟩ } ⊆ Finset.univ.erase i from ?_ ) ];
        · rw [ Finset.sum_pair ];
          · linarith;
          · norm_num [ Fin.ext_iff ];
            intro h; have := Nat.modEq_iff_dvd.mp h.symm; rcases k with ( _ | _ | k ) <;> norm_num at *;
            · contradiction;
            · contradiction;
            · linarith [ Int.le_of_dvd ( by linarith ) this ];
        · simp +decide [ Finset.subset_iff ];
          constructor <;> intro h <;> have := Fin.ext_iff.mp h <;> norm_num at this;
          · have := Nat.mod_add_div ( i + 1 ) k; simp_all +decide [ Nat.mod_eq_of_lt ] ;
            nlinarith [ show ( i : ℕ ) < k from i.2, show ( i + 1 : ℕ ) / k = 0 from by nlinarith [ show ( i : ℕ ) < k from i.2 ] ];
          · have := Nat.mod_add_div ( i + k - 1 ) k; simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ ( i : ℕ ) + k from by linarith [ Fin.is_lt i ] ) ] ;
            rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            · contradiction;
            · contradiction;
            · nlinarith [ show ( i + ( k + 1 ) ) / ( k + 1 + 1 ) = 0 by nlinarith ];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => h_sum_adj i;
    -- Since $C$ is a GCM, we know that $C (f i) (f (i+1)) \leq -1$ for all $i$, and there are $k$ such terms. Therefore, the sum of these terms is at most $-k$.
    have h_sum_adj_le_neg_k : ∑ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by linarith)⟩) + ∑ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩) ≤ -2 * k := by
      have h_sum_adj_le_neg_k : ∑ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩) ≤ -k := by
        have h_sum_adj_le_neg_k : ∀ i : Fin k, (SymmMatrix C) (f i) (f ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩) ≤ -1 := by
          intro i
          specialize h_adj ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by linarith)⟩
          simp at h_adj;
          convert h_adj using 1;
          unfold SymmMatrix; norm_num [ Nat.sub_add_cancel ( by linarith : 1 ≤ ( i : ℕ ) + k ) ] ;
          norm_num [ Fin.ext_iff, Nat.mod_eq_of_lt ];
          grind;
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_sum_adj_le_neg_k _ ) ( by norm_num );
      exact le_trans ( add_le_add ( Finset.sum_le_sum fun _ _ => h_adj _ ) h_sum_adj_le_neg_k ) ( by norm_num; linarith );
    -- Since $C$ is a GCM, we know that $C (f i) (f i) = 2$ for all $i$.
    have h_diag : ∀ i : Fin k, (SymmMatrix C) (f i) (f i) = 2 := by
      exact fun i => if_pos rfl;
    norm_num [ h_diag ] at * ; linarith;
  contrapose! h_quad_form;
  have := hP.2;
  convert this ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from ?_ ) using 1;
  · simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
  · simp +decide [ Finsupp.ext_iff ];
    exact ⟨ f ⟨ 0, by linarith ⟩, by aesop ⟩

/-! ## Forbidden star-shaped configurations -/

set_option maxHeartbeats 800000 in
/-
The T_{2,2,2} configuration (= Ẽ₆ shape) is incompatible with positive definiteness.
    f 0 = center; f 1, f 2 = arm 1; f 3, f 4 = arm 2; f 5, f 6 = arm 3.
-/
lemma no_T222 (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C)
    (f : Fin 7 ↪ Fin n)
    (h01 : C (f 0) (f 1) ≠ 0) (h12 : C (f 1) (f 2) ≠ 0)
    (h03 : C (f 0) (f 3) ≠ 0) (h34 : C (f 3) (f 4) ≠ 0)
    (h05 : C (f 0) (f 5) ≠ 0) (h56 : C (f 5) (f 6) ≠ 0) :
    ¬(SymmMatrix C).PosDef := by
  intro h;
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, x i * (SymmMatrix C) i j * x j ≤ 0 := by
    refine' ⟨ fun i => if i = f 0 then 3 else if i = f 1 then 2 else if i = f 3 then 2 else if i = f 5 then 2 else if i = f 2 then 1 else if i = f 4 then 1 else if i = f 6 then 1 else 0, _, _ ⟩ <;> simp +decide [ funext_iff ];
    · exact ⟨ f 0, by simp +decide ⟩;
    · simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] at *;
      rw [ ← Finset.sum_subset ( Finset.subset_univ { f 0, f 1, f 2, f 3, f 4, f 5, f 6 } ) ] <;> simp +decide [ Finset.sum ];
      · -- Apply the bounds on the off-diagonal entries.
        have h_off_diag : ∀ i j, i ≠ j → SymmMatrix C i j ≤ 0 := by
          exact fun i j hij => symmMatrix_off_diag_nonpos' C hG.off hG.sym hij;
        have h_off_diag : ∀ i j, i ≠ j → C i j ≠ 0 → SymmMatrix C i j ≤ -1 := by
          intros i j hij h_nonzero
          apply symmMatrix_adj_le_neg_one' C hG.off hG.sym hij h_nonzero;
        have h_off_diag : ∀ i j, i ≠ j → SymmMatrix C i j = SymmMatrix C j i := by
          intros i j hij; exact (by
          unfold SymmMatrix; simp +decide [ hij, mul_comm ] ;
          exact fun h => False.elim <| hij <| h.symm);
        have h_off_diag : SymmMatrix C (f 0) (f 0) = 2 ∧ SymmMatrix C (f 1) (f 1) = 2 ∧ SymmMatrix C (f 2) (f 2) = 2 ∧ SymmMatrix C (f 3) (f 3) = 2 ∧ SymmMatrix C (f 4) (f 4) = 2 ∧ SymmMatrix C (f 5) (f 5) = 2 ∧ SymmMatrix C (f 6) (f 6) = 2 := by
          unfold SymmMatrix; simp +decide [ hG.diag ] ;
        grind;
      · grobner;
  have := h.2;
  specialize @this ( Finsupp.equivFunOnFinite.symm x ) ; simp_all +decide [ Finsupp.sum_fintype ] ;
  exact not_lt_of_ge hx.2 ( this ( by simpa [ Finsupp.ext_iff, funext_iff ] using hx.1 ) )

set_option maxHeartbeats 800000 in
/-
The T_{1,3,3} configuration (= Ẽ₇ shape) is incompatible with positive definiteness.
    f 0 = center; f 1 = arm 1 (length 1);
    f 2, f 3, f 4 = arm 2 (length 3); f 5, f 6, f 7 = arm 3 (length 3).
-/
lemma no_T133 (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C)
    (f : Fin 8 ↪ Fin n)
    (h01 : C (f 0) (f 1) ≠ 0)
    (h02 : C (f 0) (f 2) ≠ 0) (h23 : C (f 2) (f 3) ≠ 0) (h34 : C (f 3) (f 4) ≠ 0)
    (h05 : C (f 0) (f 5) ≠ 0) (h56 : C (f 5) (f 6) ≠ 0) (h67 : C (f 6) (f 7) ≠ 0) :
    ¬(SymmMatrix C).PosDef := by
  intro hP;
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, x i * (SymmMatrix C) i j * x j ≤ 0 := by
    refine' ⟨ fun i => if i = f 0 then 4 else if i = f 1 then 2 else if i = f 2 then 3 else if i = f 3 then 2 else if i = f 4 then 1 else if i = f 5 then 3 else if i = f 6 then 2 else if i = f 7 then 1 else 0, _, _ ⟩ <;> simp +decide [ funext_iff, Finset.sum_ite ];
    · exact ⟨ f 0, by simp +decide ⟩;
    · -- By definition of $SymmMatrix$, we know that its off-diagonal entries are non-positive.
      have h_off_diag_nonpos : ∀ i j, i ≠ j → (SymmMatrix C) i j ≤ 0 := by
        exact fun i j hij => symmMatrix_off_diag_nonpos' C hG.off hG.sym hij;
      simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', hG.diag ] at *;
      -- By definition of $SymmMatrix$, we know that its diagonal entries are 2.
      have h_diag : ∀ i, SymmMatrix C i i = 2 := by
        exact fun i => if_pos rfl;
      -- By definition of $SymmMatrix$, we know that its off-diagonal entries are non-positive and symmetric.
      have h_off_diag_symm : ∀ i j, i ≠ j → SymmMatrix C i j = SymmMatrix C j i := by
        intros i j hij; exact (by
        unfold SymmMatrix; simp +decide [ hij, hG.sym ] ;
        rw [ if_neg hij.symm, mul_comm ]);
      -- By definition of $SymmMatrix$, we know that its off-diagonal entries are non-positive and symmetric, and that the diagonal entries are 2.
      have h_off_diag_le_neg_one : ∀ i j, i ≠ j → C i j ≠ 0 → SymmMatrix C i j ≤ -1 := by
        intros i j hij hCij
        have h_off_diag_le_neg_one : SymmMatrix C i j ≤ -1 := by
          apply symmMatrix_adj_le_neg_one' C hG.off hG.sym hij hCij
        exact h_off_diag_le_neg_one;
      simp_all +decide [ Fin.forall_fin_succ ];
      grind;
  have := hP.2;
  specialize @this ( Finsupp.equivFunOnFinite.symm x ) ; simp_all +decide [ Finsupp.sum_fintype ];
  exact not_lt_of_ge hx.2 ( this ( by simpa [ Finsupp.ext_iff, funext_iff ] using hx.1 ) )

set_option maxHeartbeats 800000 in
/-
The T_{1,2,5} configuration (= Ẽ₈ shape) is incompatible with positive definiteness.
    f 0 = center; f 1 = arm 1 (length 1);
    f 2, f 3 = arm 2 (length 2);
    f 4, f 5, f 6, f 7, f 8 = arm 3 (length 5).
-/
lemma no_T125 (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C)
    (f : Fin 9 ↪ Fin n)
    (h01 : C (f 0) (f 1) ≠ 0)
    (h02 : C (f 0) (f 2) ≠ 0) (h23 : C (f 2) (f 3) ≠ 0)
    (h04 : C (f 0) (f 4) ≠ 0) (h45 : C (f 4) (f 5) ≠ 0)
    (h56 : C (f 5) (f 6) ≠ 0) (h67 : C (f 6) (f 7) ≠ 0) (h78 : C (f 7) (f 8) ≠ 0) :
    ¬(SymmMatrix C).PosDef := by
  intro h_pos_def
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, (∑ i, ∑ j, x i * x j * SymmMatrix C i j) ≤ 0 ∧ ∃ i, x i ≠ 0 := by
    refine' ⟨ fun i => if i = f 0 then 6 else if i = f 1 then 3 else if i = f 2 then 4 else if i = f 3 then 2 else if i = f 4 then 5 else if i = f 5 then 4 else if i = f 6 then 3 else if i = f 7 then 2 else if i = f 8 then 1 else 0, _, _ ⟩ <;> simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ];
    · simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ] at *;
      -- Since $C$ is a GCM, we know that $SymmMatrix C i j \leq -1$ for all $i \neq j$.
      have h_symm_le_neg_one : ∀ i j, i ≠ j → C i j ≠ 0 → SymmMatrix C i j ≤ -1 := by
        exact fun i j hij h => symmMatrix_adj_le_neg_one' C hG.off hG.sym hij h;
      -- Since $C$ is a GCM, we know that $SymmMatrix C i j \leq 0$ for all $i \neq j$.
      have h_symm_le_zero : ∀ i j, i ≠ j → SymmMatrix C i j ≤ 0 := by
        intros i j hij; exact (by
        by_cases h : C i j = 0 <;> simp_all +decide [ SymmMatrix ]);
      simp +decide [ SymmMatrix ] at *;
      grind;
    · exact ⟨ f 0, by simp +decide ⟩;
  have := h_pos_def.2;
  convert this ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from fun h => hx.2.elim fun i hi => hi <| by simpa using congr_arg ( fun f => f i ) h ) using 1;
  simp +decide [ Finsupp.sum_fintype, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  simpa only [ mul_assoc ] using hx.1

/-! ## No adjacent branching vertices -/

set_option maxHeartbeats 800000 in
/-
If `u` has degree 3, no neighbor of `u` can also have degree 3.
    This implies that every branch at a degree-3 vertex is a simple path.
-/
lemma no_adjacent_degree3 (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v : Fin n) (huv : C u v ≠ 0) (hne : u ≠ v)
    (hu : 3 ≤ degree C u) (hv : 3 ≤ degree C v) :
    False := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁w₂⟩ : ∃ w₁ ∈ neighborSet C u, w₁ ≠ v ∧ ∃ w₂ ∈ neighborSet C u, w₂ ≠ v ∧ w₁ ≠ w₂ := by
    have h_card : (neighborSet C u \ {v}).card ≥ 2 := by
      grind +suggestions;
    obtain ⟨ w₁, hw₁, w₂, hw₂, hne ⟩ := Finset.one_lt_card.mp h_card; use w₁, by aesop, by aesop, w₂, by aesop, by aesop;
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁x₂⟩ : ∃ x₁ ∈ neighborSet C v, x₁ ≠ u ∧ ∃ x₂ ∈ neighborSet C v, x₂ ≠ u ∧ x₁ ≠ x₂ := by
    have h_card : (neighborSet C v \ {u}).card ≥ 2 := by
      grind +suggestions;
    obtain ⟨ x₁, hx₁, x₂, hx₂, hne ⟩ := Finset.one_lt_card.mp h_card; use x₁, by aesop, by aesop, x₂, by aesop, by aesop;
  -- By no_cycle, these vertices are distinct.
  have h_distinct : u ≠ v ∧ u ≠ w₁ ∧ u ≠ hw₂ ∧ u ≠ x₁ ∧ u ≠ hx₂ ∧ v ≠ w₁ ∧ v ≠ hw₂ ∧ v ≠ x₁ ∧ v ≠ hx₂ ∧ w₁ ≠ x₁ ∧ w₁ ≠ hx₂ ∧ hw₂ ≠ x₁ ∧ hw₂ ≠ hx₂ := by
    have h_distinct : w₁ ≠ x₁ ∧ w₁ ≠ hx₂ ∧ hw₂ ≠ x₁ ∧ hw₂ ≠ hx₂ := by
      refine' ⟨ _, _, _, _ ⟩ <;> intro h <;> simp_all +decide [ neighborSet ];
      · have := no_cycle C hG hP 3 ( by decide ) ( ⟨ fun i => if i = 0 then u else if i = 1 then v else x₁, by
          simp +decide [ Function.Injective, Fin.forall_fin_succ ];
          tauto ⟩ : Fin 3 ↪ Fin n ) ; simp_all +decide [ Fin.forall_fin_succ ];
        exact w₂.1 ( by have := hG.sym u x₁; aesop );
      · have := no_cycle C hG hP 3 ( by decide ) ( ⟨ fun i => if i = 0 then u else if i = 1 then v else hx₂, by
          simp +decide [ Function.Injective, Fin.forall_fin_succ ];
          grobner ⟩ : Fin 3 ↪ Fin n ) ; simp_all +decide [ Fin.forall_fin_succ ];
        exact w₂.1 ( by rw [ hG.sym _ _ |>.2 this ] );
      · have := no_cycle C hG hP 3 ( by decide ) ( ⟨ fun i => if i = 0 then u else if i = 1 then v else x₁, by
          simp +decide [ Function.Injective, Fin.forall_fin_succ ];
          grind ⟩ : Fin 3 ↪ Fin n ) ; simp_all +decide [ Fin.forall_fin_succ ];
        have := hG.sym u x₁; aesop;
      · have := no_cycle C hG hP 3 ( by decide ) ( ⟨ fun i => if i = 0 then u else if i = 1 then v else hx₂, by
          simp +decide [ Function.Injective, Fin.forall_fin_succ ];
          grind ⟩ : Fin 3 ↪ Fin n ) ; simp_all +decide [ Fin.forall_fin_succ ];
        have := hG.sym u hx₂; aesop;
    grind +locals;
  -- Construct test vector: x(u) = x(v) = 2, x(w₁) = x(w₂) = x(x₁) = x(x₂) = 1, x = 0 elsewhere.
  set x : Fin n → ℝ := fun i => if i = u ∨ i = v then 2 else if i = w₁ ∨ i = hw₂ ∨ i = x₁ ∨ i = hx₂ then 1 else 0;
  -- By no_cycle, these vertices are distinct, so we can apply the quadratic form argument.
  have h_quad_form : ∑ i, ∑ j, x i * x j * (SymmMatrix C) i j ≤ 0 := by
    -- By no_cycle, these vertices are distinct, so we can apply the quadratic form argument to get a contradiction.
    have h_quad_form : ∑ i ∈ ({u, v, w₁, hw₂, x₁, hx₂} : Finset (Fin n)), ∑ j ∈ ({u, v, w₁, hw₂, x₁, hx₂} : Finset (Fin n)), x i * x j * (SymmMatrix C) i j ≤ 0 := by
      have h_quad_form : ∀ i ∈ ({u, v, w₁, hw₂, x₁, hx₂} : Finset (Fin n)), ∀ j ∈ ({u, v, w₁, hw₂, x₁, hx₂} : Finset (Fin n)), i ≠ j → (SymmMatrix C) i j ≤ if i = u ∧ j = v ∨ i = v ∧ j = u then -1 else if i = u ∧ j = w₁ ∨ i = w₁ ∧ j = u ∨ i = u ∧ j = hw₂ ∨ i = hw₂ ∧ j = u then -1 else if i = v ∧ j = x₁ ∨ i = x₁ ∧ j = v ∨ i = v ∧ j = hx₂ ∨ i = hx₂ ∧ j = v then -1 else 0 := by
        intros i hi j hj hij
        have h_adj : C i j ≠ 0 → (SymmMatrix C) i j ≤ -1 := by
          apply symmMatrix_adj_le_neg_one' C hG.off hG.sym hij;
        split_ifs <;> simp_all +decide [ neighborSet ];
        · cases ‹_› <;> simp_all +decide [ IsGCM'.sym ];
        · rcases ‹_› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ IsGCM'.sym ];
        · rcases ‹_› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ IsGCM'.sym ];
        · exact symmMatrix_off_diag_nonpos' C ( fun i j hij => hG.off i j hij ) ( fun i j => hG.sym i j ) ( by aesop );
      refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => _ ) _;
      use fun i j => if i = j then x i * x j * 2 else x i * x j * ( if i = u ∧ j = v ∨ i = v ∧ j = u then -1 else if i = u ∧ j = w₁ ∨ i = w₁ ∧ j = u ∨ i = u ∧ j = hw₂ ∨ i = hw₂ ∧ j = u then -1 else if i = v ∧ j = x₁ ∨ i = x₁ ∧ j = v ∨ i = v ∧ j = hx₂ ∨ i = hx₂ ∧ j = v then -1 else 0 );
      · by_cases hij : i = j <;> simp +decide [ hij ];
        · unfold SymmMatrix; norm_num;
        · convert mul_le_mul_of_nonneg_left ( h_quad_form i hi j hj hij ) ( show 0 ≤ x i * x j by positivity ) using 1 ; ring;
          split_ifs <;> ring;
      · simp +decide [ Finset.sum_ite, Finset.filter_ne, Finset.filter_eq, * ];
        simp +decide [ Finset.sum_filter, Finset.sum_erase, * ];
        grind +splitIndPred;
    refine le_trans ?_ h_quad_form;
    rw [ ← Finset.sum_subset ( Finset.subset_univ { u, v, w₁, hw₂, x₁, hx₂ } ) ];
    · refine' Finset.sum_le_sum fun i hi => _;
      rw [ ← Finset.sum_subset ( Finset.subset_univ { u, v, w₁, hw₂, x₁, hx₂ } ) ];
      grind;
    · simp +zetaDelta at *;
      intro i hi₁ hi₂ hi₃ hi₄ hi₅ hi₆; simp +decide [ hi₁, hi₂, hi₃, hi₄, hi₅, hi₆ ] ;
  contrapose! h_quad_form;
  have := hP.2;
  convert this ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from ?_ ) using 1;
  · simp +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ];
  · simp +decide [ Finsupp.ext_iff, x ];
    exact ⟨ u, by aesop ⟩

/-! ## Degree of neighbors in a branch -/

set_option maxHeartbeats 800000 in
/-
Every vertex has degree at most 3 (restated for use here).
-/
lemma pos_degree_le_three' (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef) (i : Fin n) :
    degree C i ≤ 3 := by
  -- By contradiction, assume degree C i ≥ 4. Then the neighbor set N has card ≥ 4.
  by_contra h_contra
  obtain ⟨N, hN⟩ : ∃ N : Finset (Fin n), N.card ≥ 4 ∧ ∀ j ∈ N, C i j ≠ 0 ∧ i ≠ j := by
    exact ⟨ _, not_le.mp h_contra, fun j hj => by aesop ⟩;
  -- Show ∑ a, ∑ b, x a * SymmMatrix C a b * x b ≤ 0:
  have h_quad_form : ∑ a, ∑ b, (if a = i then 2 else if a ∈ N then 1 else 0) * (SymmMatrix C a b) * (if b = i then 2 else if b ∈ N then 1 else 0) ≤ 0 := by
    -- Split the sum into diagonal and off-diagonal parts.
    have h_split : ∑ a, ∑ b, (if a = i then 2 else if a ∈ N then 1 else 0) * (SymmMatrix C a b) * (if b = i then 2 else if b ∈ N then 1 else 0) =
      (2 * (SymmMatrix C i i) * 2) + (∑ j ∈ N, (1 * (SymmMatrix C j j) * 1)) +
      (∑ j ∈ N, (2 * (SymmMatrix C i j) * 1)) + (∑ j ∈ N, (1 * (SymmMatrix C j i) * 2)) +
      (∑ j ∈ N, ∑ k ∈ N, (1 * (SymmMatrix C j k) * 1) - ∑ j ∈ N, (1 * (SymmMatrix C j j) * 1)) := by
        simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', Finset.filter_and, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ] ; ring!;
        by_cases hi : i ∈ N <;> simp_all +decide [ Finset.sum_erase ];
        exact False.elim <| hN.2 i hi |>.2 rfl;
    -- Apply the bounds on the diagonal and off-diagonal entries.
    have h_bounds : ∀ j ∈ N, SymmMatrix C i j ≤ -1 ∧ SymmMatrix C j i ≤ -1 ∧ SymmMatrix C j j = 2 := by
      intros j hj
      have h_off_diag : SymmMatrix C i j ≤ -1 ∧ SymmMatrix C j i ≤ -1 := by
        have h_off_diag : ∀ i j, i ≠ j → C i j ≠ 0 → SymmMatrix C i j ≤ -1 := by
          intros i j hij hCij
          apply symmMatrix_adj_le_neg_one' C hG.off hG.sym hij hCij;
        exact ⟨ h_off_diag i j ( hN.2 j hj |>.2 ) ( hN.2 j hj |>.1 ), h_off_diag j i ( Ne.symm ( hN.2 j hj |>.2 ) ) ( by have := hG.sym i j; aesop ) ⟩
      have h_diag : SymmMatrix C j j = 2 := by
        exact if_pos rfl
      exact ⟨h_off_diag.left, h_off_diag.right, h_diag⟩;
    -- Apply the bounds on the off-diagonal entries.
    have h_off_diag_bounds : ∑ j ∈ N, ∑ k ∈ N, (1 * (SymmMatrix C j k) * 1) ≤ 2 * N.card := by
      have h_off_diag_bounds : ∀ j k : Fin n, j ≠ k → SymmMatrix C j k ≤ 0 := by
        exact fun j k hjk => symmMatrix_off_diag_nonpos' C hG.off hG.sym hjk;
      have h_off_diag_bounds : ∑ j ∈ N, ∑ k ∈ N, (1 * (SymmMatrix C j k) * 1) ≤ ∑ j ∈ N, (SymmMatrix C j j) := by
        rw [ Finset.sum_congr rfl fun j hj => Finset.sum_eq_add_sum_diff_singleton hj _ ];
        exact Finset.sum_le_sum fun j hj => by simpa using Finset.sum_nonpos fun k hk => h_off_diag_bounds j k <| by aesop;
      exact h_off_diag_bounds.trans ( by rw [ Finset.sum_congr rfl fun x hx => h_bounds x hx |>.2.2 ] ; norm_num; linarith );
    simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
    rw [ show SymmMatrix C i i = 2 by exact if_pos rfl ] ; norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at * ; nlinarith [ show ( N.card : ℝ ) ≥ 4 by exact_mod_cast hN.1, show ( ∑ j ∈ N, SymmMatrix C i j : ℝ ) ≤ -N.card by exact le_trans ( Finset.sum_le_sum fun x hx => h_bounds x hx |>.1 ) ( by norm_num ), show ( ∑ j ∈ N, SymmMatrix C j i : ℝ ) ≤ -N.card by exact le_trans ( Finset.sum_le_sum fun x hx => h_bounds x hx |>.2.1 ) ( by norm_num ) ] ;
  have := hP.2;
  specialize @this ( Finsupp.equivFunOnFinite.symm ( fun j => if j = i then 2 else if j ∈ N then 1 else 0 ) ) ; simp_all +decide [ Finsupp.sum_fintype ];
  exact not_lt_of_ge h_quad_form ( this ( by intro h; have := congr_arg ( fun f => f i ) h; norm_num at this ) )


/-! ## Branch structure lemmas -/

/-
If `branchSize ≥ 2`, the branch root `v` has a neighbor in the branch besides `u`.
-/
lemma branch_ge2_has_neighbor (C : Matrix (Fin n) (Fin n) ℤ)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    (u v : Fin n) (hvu : v ≠ u) (hbs : branchSize C u v ≥ 2) :
    ∃ w, w ≠ v ∧ w ≠ u ∧ C v w ≠ 0 ∧ w ∈ branchSet C u v := by
  -- Since `branchSize C u v` is at least 2, there exists some `w` in `branchSet C u v` such that `w ≠ v`.
  obtain ⟨w, hw⟩ : ∃ w ∈ branchSet C u v, w ≠ v := by
    contrapose! hbs; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
    exact lt_of_le_of_lt ( Set.ncard_le_ncard ( show branchSet C u v ⊆ { v } from fun x hx => hbs x hx ) ) ( by norm_num );
  -- Since `w ∈ branchSet C u v`, we have `TransGen (adjExcl C u) v w`.
  obtain ⟨z, hz⟩ : ∃ z, adjExcl C u v z ∧ reachExcl C u z w := by
    obtain ⟨z, hz⟩ : ∃ z, adjExcl C u v z ∧ reachExcl C u z w := by
      have h_trans : Relation.ReflTransGen (adjExcl C u) v w := by
        exact hw.1
      have := h_trans.cases_head;
      tauto;
    use z;
  use z;
  exact ⟨ hz.1.1.symm, hz.1.2.2.1, hz.1.2.2.2, by exact Relation.ReflTransGen.single hz.1 ⟩

set_option maxHeartbeats 800000 in
/-- Two degree-3 vertices connected by a simple path cannot coexist
    in a GCM with positive definite symmetrization.
    `z : Fin (d+1) ↪ Fin n` is the path, `z 0` and `z d` both have degree ≥ 3. -/
lemma no_two_branching_via_path (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (d : ℕ) (hd : d ≥ 1)
    (z : Fin (d + 1) ↪ Fin n)
    (hpath : ∀ i : Fin d, C (z i.castSucc) (z i.succ) ≠ 0)
    (hu : 3 ≤ degree C (z ⟨0, by omega⟩))
    (hw : 3 ≤ degree C (z ⟨d, by omega⟩)) :
    False := by
  sorry

/-
In a positive-definite GCM, if `u` has degree 3 and `v` is a neighbor of `u`,
    then `v` has at most 1 neighbor other than `u`
    (i.e., `v` has degree ≤ 2 in the full graph).
-/
lemma neighbor_of_deg3_has_low_degree (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v : Fin n) (huv : C u v ≠ 0) (hne : u ≠ v)
    (hu : degree C u = 3) :
    degree C v ≤ 2 := by
  by_contra h_contra;
  exact no_adjacent_degree3 C hG hP u v huv hne ( by linarith ) ( by linarith )

/-- In a positive-definite GCM with a degree-3 vertex `u`, no vertex `w` reachable
    from a neighbor `v` of `u` (avoiding `u`) can have degree ≥ 3.
    This means every branch is a simple path. -/
lemma branch_vertex_has_low_degree (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v : Fin n) (huv : C u v ≠ 0) (hne : u ≠ v)
    (hu : degree C u = 3) (w : Fin n) (hw : w ∈ branchSet C u v) :
    degree C w ≤ 2 := by
  sorry

/-- In a positive-definite GCM, if a branch has size ≥ k, there is a simple path
    of length k-1 starting from the branch root through the branch. -/
lemma branch_has_path (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v : Fin n) (huv : C u v ≠ 0) (hne : u ≠ v) (hu : degree C u = 3)
    (k : ℕ) (hk : k ≥ 1) (hbs : branchSize C u v ≥ k) :
    ∃ f : Fin k ↪ Fin n,
      f ⟨0, by omega⟩ = v ∧
      (∀ i : Fin k, ∀ j : Fin k, i.val + 1 = j.val → C (f i) (f j) ≠ 0) ∧
      (∀ i, f i ≠ u) := by
  sorry

/-
If the only non-u neighbors of both v and x are each other,
    then the set reachable from x via adjExcl C u is contained in {x, v}.
-/
lemma reachable_of_pair_bounded (C : Matrix (Fin n) (Fin n) ℤ)
    (hsym : ∀ i j, C i j = 0 ↔ C j i = 0)
    (u v x : Fin n) (hvx : v ≠ x) (hvu : v ≠ u) (hxu : x ≠ u)
    (hv_nbrs : ∀ j, j ≠ v → j ≠ u → C v j ≠ 0 → j = x)
    (hx_nbrs : ∀ j, j ≠ x → j ≠ u → C x j ≠ 0 → j = v)
    (w : Fin n) (hw : Relation.ReflTransGen (adjExcl C u) x w) :
    w = x ∨ w = v := by
  induction hw;
  · exact Or.inl rfl;
  · grind +locals

/-- If w is reachable from both v₁ and v₂ (avoiding u), and v₁ ≠ v₂ are both neighbors
    of u, then we get a cycle, which is impossible. -/
lemma branches_disjoint (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v₁ v₂ : Fin n) (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂)
    (w : Fin n) (hw₁ : w ∈ branchSet C u v₁) (hw₂ : w ∈ branchSet C u v₂) :
    False := by
  sorry

/-
If a branch has size ≥ 3 and u has degree 3, then the branch root v has a
    path v - x - y of length 2 in the branch (with all three vertices distinct
    and different from u).
-/
lemma branch_ge3_has_path2 (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u v : Fin n) (huv : C u v ≠ 0) (hne : u ≠ v) (hu : degree C u = 3)
    (hbs : branchSize C u v ≥ 3) :
    ∃ x y, x ≠ v ∧ x ≠ u ∧ y ≠ v ∧ y ≠ u ∧ y ≠ x ∧
           C v x ≠ 0 ∧ C x y ≠ 0 ∧
           x ∈ branchSet C u v ∧ y ∈ branchSet C u v := by
  -- Apply the branch_has_path lemma to get a path of length 2 in the branch.
  obtain ⟨f, hf⟩ : ∃ f : Fin 3 ↪ Fin n, f ⟨0, by omega⟩ = v ∧ (∀ i : Fin 3, ∀ j : Fin 3, i.val + 1 = j.val → C (f i) (f j) ≠ 0) ∧ (∀ i, f i ≠ u) := by
    apply branch_has_path C hG hP u v huv hne hu 3 (by omega) hbs;
  refine' ⟨ f ⟨ 1, by decide ⟩, f ⟨ 2, by decide ⟩, _, _, _, _, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ ];
  · exact fun h => by have := f.injective ( h.trans hf.1.symm ) ; contradiction;
  · aesop;
  · grind +locals

/-! ## Main branch bound theorems -/

/-
The smallest branch at a degree-3 vertex has exactly 1 vertex.
-/
theorem smallest_branch_eq_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃) :
    branchSize C u v₁ = 1 := by
  by_contra h_contra;
  -- By branch_ge2_has_neighbor (applied to each vᵢ), for each i there exists wᵢ with:
  -- wᵢ ≠ vᵢ, wᵢ ≠ u, C vᵢ wᵢ ≠ 0.
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≠ v₁ ∧ w₁ ≠ u ∧ v₁ ≠ u ∧ C v₁ w₁ ≠ 0 ∧ w₁ ∈ branchSet C u v₁ := by
    have := branch_ge2_has_neighbor C hG.sym u v₁ (by
    exact fun h => by simp_all +decide [ neighborSet ] ;) (by
    exact Nat.lt_of_le_of_ne ( by exact Nat.succ_le_of_lt ( by exact Nat.pos_of_ne_zero ( by exact Set.ncard_ne_zero_of_mem ( show v₁ ∈ branchSet C u v₁ from Relation.ReflTransGen.refl ) ) ) ) ( Ne.symm h_contra ));
    unfold neighborSet at hv₁; aesop;
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ ≠ v₂ ∧ w₂ ≠ u ∧ v₂ ≠ u ∧ C v₂ w₂ ≠ 0 ∧ w₂ ∈ branchSet C u v₂ := by
    have := branch_ge2_has_neighbor C ( fun i j => hG.sym i j ) u v₂ ( by
      exact fun h => by simp_all +decide [ neighborSet ] ; ) ( by
      exact Nat.lt_of_le_of_ne ( Nat.succ_le_of_lt ( show branchSize C u v₁ > 0 from by
                                                      exact Nat.pos_of_ne_zero ( by unfold branchSize; exact Set.ncard_ne_zero_of_mem ( show v₁ ∈ { w | reachExcl C u v₁ w } from Relation.ReflTransGen.refl ) ) ) ) ( Ne.symm h_contra ) |> le_trans <| hsort.1 );
    exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, by rintro rfl; exact absurd ( Finset.mem_filter.mp hv₂ |>.2.2 ) ( by simp +decide ), this.choose_spec.2.2.1, this.choose_spec.2.2.2 ⟩
  obtain ⟨w₃, hw₃⟩ : ∃ w₃, w₃ ≠ v₃ ∧ w₃ ≠ u ∧ v₃ ≠ u ∧ C v₃ w₃ ≠ 0 ∧ w₃ ∈ branchSet C u v₃ := by
    convert branch_ge2_has_neighbor C ( fun i j => by exact hG.sym i j ) u v₃ _ _ using 1;
    · ext; simp [hv₃];
      exact fun _ _ _ _ => by rintro rfl; exact absurd hv₃ ( by simp +decide [ neighborSet ] ) ;
    · exact fun h => by simp_all +decide [ neighborSet ] ;
    · exact le_trans ( Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by
        intro h; simp_all +decide [ branchSize ] ;
        rw [ @Set.ncard_eq_zero ] at h;
        · exact h.subset hw₁.2.2.2.2;
        · exact Set.toFinite _ ) ) ) ( Ne.symm h_contra ) ) ) ( hsort.1.trans hsort.2 );
  -- Show all 7 vertices {u, v₁, w₁, v₂, w₂, v₃, w₃} are distinct.
  have h_distinct : u ≠ v₁ ∧ u ≠ v₂ ∧ u ≠ v₃ ∧ u ≠ w₁ ∧ u ≠ w₂ ∧ u ≠ w₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ w₁ ∧ v₁ ≠ w₂ ∧ v₁ ≠ w₃ ∧ v₂ ≠ v₃ ∧ v₂ ≠ w₁ ∧ v₂ ≠ w₂ ∧ v₂ ≠ w₃ ∧ v₃ ≠ w₁ ∧ v₃ ≠ w₂ ∧ v₃ ≠ w₃ ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ := by
    have h_distinct : w₁ ≠ v₂ ∧ w₁ ≠ v₃ ∧ w₂ ≠ v₁ ∧ w₂ ≠ v₃ ∧ w₃ ≠ v₁ ∧ w₃ ≠ v₂ := by
      have h_distinct : ∀ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ k ≠ i → C i j ≠ 0 → C j k ≠ 0 → C k i ≠ 0 → False := by
        intros i j k hij hik hjk hkj
        have := no_cycle C hG hP 3 (by decide) (Function.Embedding.mk ![i, j, k] (by
        simp +decide [ Function.Injective, Fin.forall_fin_succ ];
        grind)) (by
        simp +decide [ Fin.forall_fin_succ, * ])
        aesop;
      simp_all +decide [ neighborSet ];
      have := hG.sym u v₁; have := hG.sym u v₂; have := hG.sym u v₃; have := hG.sym v₁ w₁; have := hG.sym v₂ w₂; have := hG.sym v₃ w₃; simp_all +decide [ IsGCM' ] ;
      grind +ring;
    have h_distinct : w₁ ≠ w₂ := by
      rintro rfl;
      have h_cycle : C u v₁ ≠ 0 ∧ C v₁ w₁ ≠ 0 ∧ C w₁ v₂ ≠ 0 ∧ C v₂ u ≠ 0 := by
        simp_all +decide [ neighborSet ];
        exact ⟨ by have := hG.sym w₁ v₂; aesop, by have := hG.sym v₂ u; aesop ⟩;
      have h_cycle : ∃ f : Fin 4 ↪ Fin n, f 0 = u ∧ f 1 = v₁ ∧ f 2 = w₁ ∧ f 3 = v₂ ∧ ∀ i : Fin 4, C (f i) (f ⟨(i.val + 1) % 4, Nat.mod_lt _ (by omega)⟩) ≠ 0 := by
        use ⟨![u, v₁, w₁, v₂], by
          simp +decide [ Function.Injective, Fin.forall_fin_succ ];
          grind⟩
        generalize_proofs at *;
        simp_all +decide [ Fin.forall_fin_succ ];
      obtain ⟨ f, hf₀, hf₁, hf₂, hf₃, hf₄ ⟩ := h_cycle;
      exact no_cycle C hG hP 4 ( by decide ) f hf₄
    have h_distinct' : w₁ ≠ w₃ := by
      rintro rfl;
      apply no_cycle C hG hP 4 (by decide) (Function.Embedding.mk (fun i => if i = 0 then u else if i = 1 then v₁ else if i = 2 then w₁ else v₃) (by
      simp +decide [ Function.Injective, Fin.forall_fin_succ ];
      grind)) (by
      simp +decide [ Fin.forall_fin_succ ];
      simp_all +decide [ neighborSet ];
      exact ⟨ by have := hG.sym w₁ v₃; aesop, by have := hG.sym v₃ u; aesop ⟩)
    have h_distinct'' : w₂ ≠ w₃ := by
      intro h_eq;
      have h_cycle : C u v₂ ≠ 0 ∧ C v₂ w₃ ≠ 0 ∧ C w₃ v₃ ≠ 0 ∧ C v₃ u ≠ 0 := by
        simp_all +decide [ neighborSet ];
        exact ⟨ by have := hG.sym v₃ w₃; aesop, by have := hG.sym u v₃; aesop ⟩;
      have := no_cycle C hG hP 4 ( by decide ) ( ⟨ ![u, v₂, w₃, v₃], by
        simp +decide [ Function.Injective, Fin.forall_fin_succ ];
        grind +splitImp ⟩ : Fin 4 ↪ Fin n ) ; simp_all +decide;
      obtain ⟨ x, hx ⟩ := this; fin_cases x <;> simp_all +decide ;
    grind;
  apply no_T222 C hG (Function.Embedding.mk ![u, v₁, w₁, v₂, w₂, v₃, w₃] (by
  simp +decide [ Function.Injective, Fin.forall_fin_succ ];
  grind +qlia)) (by
  unfold neighborSet at hv₁; aesop;) (by
  exact hw₁.2.2.2.1) (by
  simp_all +decide [ neighborSet ]) (by
  exact hw₂.2.2.2.1) (by
  exact Finset.mem_filter.mp hv₃ |>.2.1) (by
  exact hw₃.2.2.2.1);
  assumption

/-
The second-smallest branch at a degree-3 vertex has at most 2 vertices.
-/
theorem second_branch_le_two (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃) :
    branchSize C u v₂ ≤ 2 := by
  by_contra! hcontr;
  -- Use `branch_ge3_has_path2` on both `v₂` and `v₃` (with `hG`, `hP`, `u`, `vᵢ`, `C u vᵢ ≠ 0`, `u ≠ vᵢ`, `degree u = 3`, `branchSize ≥ 3`) to get:
  obtain ⟨x₂, y₂, hx₂, hy₂, hxy₂⟩ := branch_ge3_has_path2 C hG hP u v₂ (by
  exact Finset.mem_filter.mp hv₂ |>.2.1) (by
  unfold neighborSet at hv₂; aesop;) hu (by
  finiteness)
  obtain ⟨x₃, y₃, hx₃, hy₃, hxy₃⟩ := branch_ge3_has_path2 C hG hP u v₃ (by
  exact Finset.mem_filter.mp hv₃ |>.2.1) (by
  exact fun h => by simp_all +decide [ neighborSet ] ;) hu (by
  linarith);
  -- By the properties of the branch, we know that $x₂ \neq v₁$, $y₂ \neq v₁$, $x₃ \neq v₁$, and $y₃ \neq v₁$.
  have hx₂_ne_v₁ : x₂ ≠ v₁ := by
    rintro rfl;
    apply branches_disjoint C hG hP u v₂ x₂ hv₂ hv₁ (by tauto) x₂ (by tauto) (by tauto)
  have hy₂_ne_v₁ : y₂ ≠ v₁ := by
    intro H; simp_all +decide [ neighborSet ] ;
    have := branches_disjoint C hG hP u v₂ v₁; simp_all +decide [ branchSet ] ;
    exact this ( by unfold neighborSet; aesop ) ( by unfold neighborSet; aesop ) ( by tauto ) v₁ ( by tauto ) ( by tauto )
  have hx₃_ne_v₁ : x₃ ≠ v₁ := by
    intro H; simp_all +decide [ branchSet ] ;
    apply branches_disjoint C hG hP u v₃ v₁ hv₃ hv₁ (by tauto) v₁ (by tauto) (by tauto)
  have hy₃_ne_v₁ : y₃ ≠ v₁ := by
    intro h; simp_all +decide [ branchSet ] ;
    apply branches_disjoint C hG hP u v₃ v₁ hv₃ hv₁ (by tauto) v₁ (by tauto) (by tauto);
  -- By the properties of the branch, we know that $x₂ \neq v₃$, $x₃ \neq v₂$, $x₂ \neq x₃$, $y₂ \neq v₃$, $y₃ \neq v₂$, $x₂ \neq y₃$, $y₂ \neq x₃$, and $y₂ \neq y₃$.
  have hx₂_ne_v₃ : x₂ ≠ v₃ := by
    intro h;
    have := branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₃ ; simp_all +decide [ branchSet ];
    exact this ( Relation.ReflTransGen.refl )
  have hx₃_ne_v₂ : x₃ ≠ v₂ := by
    rintro rfl;
    apply branches_disjoint C hG hP u x₃ v₃ hv₂ hv₃ (by tauto) x₃ (by tauto) (by tauto)
  have hx₂_ne_x₃ : x₂ ≠ x₃ := by
    rintro rfl;
    apply branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ hdist.2.2 x₂ hxy₂.2.2.2.2.2.1 hxy₃.2.2.2.2.2.1
  have hy₂_ne_v₃ : y₂ ≠ v₃ := by
    intro h; simp_all +decide [ branchSet ] ;
    exact branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₃ ( by tauto ) ( by tauto )
  have hy₃_ne_v₂ : y₃ ≠ v₂ := by
    intro h; simp_all +decide [ branchSet ] ;
    have := branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₂ ( by tauto ) ( by tauto ) ; simp_all +decide [ branchSet ] ;
  have hx₂_ne_y₃ : x₂ ≠ y₃ := by
    intro h; simp_all +decide [ branchSet ] ;
    have := branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₃; simp_all +decide [ branchSet ] ;
  have hy₂_ne_x₃ : y₂ ≠ x₃ := by
    rintro rfl;
    apply branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₂ hxy₂.2.2.2.2.2.2 hxy₃.2.2.2.2.2.1
  have hy₂_ne_y₃ : y₂ ≠ y₃ := by
    rintro rfl;
    apply branches_disjoint C hG hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₂ hxy₂.2.2.2.2.2.2 hxy₃.2.2.2.2.2.2;
  -- Construct the embedding $f : Fin 8 ↪ Fin n$ with the specified properties.
  obtain ⟨f, hf⟩ : ∃ f : Fin 8 ↪ Fin n, f 0 = u ∧ f 1 = v₁ ∧ f 2 = v₂ ∧ f 3 = x₂ ∧ f 4 = y₂ ∧ f 5 = v₃ ∧ f 6 = x₃ ∧ f 7 = y₃ := by
    use ⟨![u, v₁, v₂, x₂, y₂, v₃, x₃, y₃], by
      simp +decide [ Function.Injective, Fin.forall_fin_succ ];
      grind +locals⟩
    generalize_proofs at *;
    exact ⟨ rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl ⟩;
  have h_adj : C (f 0) (f 1) ≠ 0 ∧ C (f 0) (f 2) ≠ 0 ∧ C (f 2) (f 3) ≠ 0 ∧ C (f 3) (f 4) ≠ 0 ∧ C (f 0) (f 5) ≠ 0 ∧ C (f 5) (f 6) ≠ 0 ∧ C (f 6) (f 7) ≠ 0 := by
    simp_all +decide [ neighborSet ];
  exact no_T133 C hG f h_adj.1 h_adj.2.1 h_adj.2.2.1 h_adj.2.2.2.1 h_adj.2.2.2.2.1 h_adj.2.2.2.2.2.1 h_adj.2.2.2.2.2.2 hP

/-- The largest branch at a degree-3 vertex has at most 4 vertices, provided
    the second-largest branch has at least 2 vertices.
    NOTE: The unconditional bound c ≤ 4 is FALSE: D_n with n ≥ 8 has
    branch sizes (1, 1, n-3) where n-3 ≥ 5. The bound only holds when b ≥ 2. -/
theorem largest_branch_le_four (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃)
    (hb : branchSize C u v₂ ≥ 2) :
    branchSize C u v₃ ≤ 4 := by
  sorry

/-- Combined branch bound: at a degree-3 vertex with sorted branch sizes a ≤ b ≤ c,
    we have a = 1, b ≤ 2, and if b ≥ 2 then c ≤ 4. -/
theorem branch_bounds (C : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsGCM' C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃) :
    branchSize C u v₁ = 1 ∧ branchSize C u v₂ ≤ 2 ∧
    (branchSize C u v₂ ≥ 2 → branchSize C u v₃ ≤ 4) :=
  ⟨smallest_branch_eq_one C hG hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist hsort,
   second_branch_le_two C hG hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist hsort,
   fun hb => largest_branch_le_four C hG hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist hsort hb⟩

end CartanMatrix