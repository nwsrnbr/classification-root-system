import Mathlib

open CartanMatrix
open Matrix

variable (n : ℕ)

def D_rev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

def D_rev' (n : ℕ) :=
  Matrix.of fun i j : Fin n ↦ D n (i.rev) (j.rev)

lemma D_rev_eq (n : ℕ) : D_rev n = D_rev' n := by
  ext i j
  simp [D_rev, D_rev', D, Fin.rev]
  split_ifs
  <;> grind

lemma D_rev_eq' (n : ℕ) : D_rev' n =
    let e := Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective
  (reindex e e) (D n) := by
  ext i j
  simp [D_rev', reindex, Equiv.ofBijective, Function.surjInv]
  grind

@[simp]
lemma det_D_rev (n : ℕ) : det (D_rev n) = det (D n) := by
  simp [D_rev_eq, D_rev_eq']

/-- The Cartan matrix of type D_tildaₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o                       o
     \                     /
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /                     \
    o                       o
```
-/
def D_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (D_rev n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 2 = i then -1
    else if (i : ℕ) + 2 = j then -1
    else 0

/-- Null vector for D_tilda: entries are 1,1,2,2,...,2,1,1 -/
noncomputable def D_tilda_null_vec (n : ℕ) : Fin (n + 1) → ℤ := fun i =>
  if i.val = 0 ∨ i.val = 1 then 1
  else if i.val = n - 1 ∨ i.val = n then 1
  else 2

lemma D_tilda_null_vec_ne_zero (n : ℕ) (hn : n ≥ 2) : D_tilda_null_vec n ≠ 0 := by
  exact fun h => absurd ( congr_fun h 0 ) ( by norm_num [ D_tilda_null_vec ] ) ;

set_option maxHeartbeats 800000 in
lemma D_tilda_mulVec_null (n : ℕ) (hn : n ≥ 4) :
    (D_tilda n).mulVec (D_tilda_null_vec n) = 0 := by
  rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ Fin.sum_univ_succ, D_tilda ];
  ext i; simp +decide [ *, Matrix.mulVec, dotProduct ] ;
  rw [ Finset.sum_fin_eq_sum_range ] ; norm_num [ Finset.sum_range_succ', D_rev, D_tilda_null_vec ] ; ring;
  rcases i with ⟨ _ | _ | _ | _ | _ | i, hi ⟩ <;> norm_num [ Fin.ext_iff, Fin.castLT ] at *;
  all_goals simp +arith +decide [ Finset.sum_ite ] at *;
  · grind +qlia;
  · grind;
  · grind;
  · rcases n with ( _ | _ | _ | _ | n ) <;> simp +arith +decide [ Finset.filter_eq', Finset.filter_ne' ] at *;
    · aesop;
    · interval_cases i <;> trivial;
    · interval_cases i <;> trivial;
    · rcases hi with ( _ | _ | _ | hi ) <;> simp +arith +decide [ Finset.filter_eq', Finset.filter_ne' ] at *;
      · simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ];
        simp +arith +decide [ Finset.filter_singleton ];
      · simp +arith +decide [ Finset.filter_eq', Finset.filter_or, Finset.filter_and ];
        simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ];
      · simp +arith +decide [ Finset.filter_eq', Finset.filter_or, Finset.filter_and ] at *;
        simp +arith +decide [ Finset.filter_singleton, Finset.filter_insert, Finset.filter_inter ] at *;
        simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ] at *;
        intros; omega;
      · split_ifs <;> try linarith;
        any_goals omega;
        · simp_all +decide [ Finset.filter_eq', Finset.filter_or, Finset.filter_and ];
          simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ];
        · rcases i with ( _ | _ | i ) <;> simp +arith +decide [ Finset.filter_eq', Finset.filter_ne' ] at *;
          · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Finset.filter_eq', Finset.filter_ne' ] at *;
            simp +arith +decide [ Finset.filter_eq', Finset.filter_or, Finset.filter_and ] at *;
            simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ] at *;
          · simp +arith +decide [ Finset.filter_eq', Finset.filter_or, Finset.filter_and ];
            simp +arith +decide [ Finset.filter_eq, Finset.filter_ne ];
            grind

lemma det_D_tilda_eq_zero (n : ℕ) (hn : n ≥ 4) : (D_tilda n).det = 0 := by
  -- Use `Matrix.exists_mulVec_eq_zero_iff.mp` with the witness `D_tilda_null_vec n` and the lemmas `D_tilda_mulVec_null` and `D_tilda_null_vec_ne_zero`.
  have h := Matrix.exists_mulVec_eq_zero_iff.mp (by
  use D_tilda_null_vec n;
  exact ⟨ D_tilda_null_vec_ne_zero n ( by linarith ), D_tilda_mulVec_null n ( by linarith ) ⟩ : ∃ v : Fin (n + 1) → ℤ, v ≠ 0 ∧ (D_tilda n).mulVec v = 0);
  aesop;

theorem det_D_tilda (n : ℕ) (h0 : ¬n = 0) (h1 : ¬n = 1) (v : Fin (n + 1) → ℤ := fun x ↦ 1) :
    (D_tilda n).det =
  if n = 0 then 2
  else if n = 1 then 4
  else if n = 2 then 6
  else if n = 3 then 5
  else 0 := by
  rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide;
  exact det_D_tilda_eq_zero _ le_add_self