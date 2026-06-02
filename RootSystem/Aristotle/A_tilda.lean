import Mathlib

open CartanMatrix

def a' (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if i = 0 ∧ j = n ∨ j = 0 ∧ i = n then -1
    else 0



/- The original theorem below is false. The definition `a'` is not the affine Cartan matrix
   of type Ã_n because it is missing the adjacency between node `n` and node `n-1`.
   As a result, `(a' n).det = n + 2`, not `0`. For example:
   - `(a' 2).det = 4`
   - `(a' 3).det = 5`

   The corrected definition `a'C` below adds the missing entries `(n-1, n)` and `(n, n-1)`,
   making it the proper affine Cartan matrix whose determinant is indeed `0`.
-/
-- theorem det_a' (n : ℕ) (h0 : ¬n = 0) (h1 : ¬n = 1) (v : Fin (n + 1) → ℤ := fun x ↦ 1) :
--     (a' n).det = 0 := by
--   sorry

/-- The corrected affine Cartan matrix of type Ã_n.
    Compared to `a'`, this adds the adjacency between node `n` and node `n-1`. -/
def a'C (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (i.val = 0 ∧ j.val = n) ∨ (j.val = 0 ∧ i.val = n) ∨
            (i.val = n - 1 ∧ j.val = n) ∨ (j.val = n - 1 ∧ i.val = n) then -1
    else 0

lemma a'C_mulVec_one (n : ℕ) (h0 : ¬n = 0) (h1 : ¬n = 1) :
    (a'C n).mulVec (fun _ => 1) = 0 := by
      rcases n with ( _ | _ | n ) <;> simp_all +decide;
      ext i; simp [a'C, Matrix.mulVec];
      simp +decide [ A, dotProduct ];
      by_cases hi : ( i : ℕ ) ≤ n + 1 <;> simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_or, Finset.filter_and, hi ];
      · rw [ Finset.sum_fin_eq_sum_range ];
        rcases i with ⟨ _ | i, hi ⟩ <;> norm_num [ Finset.sum_range_succ', Fin.ext_iff ];
        · rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range_succ ];
          rw [ Finset.sum_congr rfl fun x hx => by rw [ if_pos ( by linarith [ Finset.mem_range.mp hx ] ), if_pos ( by linarith [ Finset.mem_range.mp hx ] ) ] ] ; norm_num;
        · rcases i with ( _ | _ | i ) <;> simp_all +decide [ Finset.sum_ite ];
          · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.filter_eq', Finset.filter_and ];
          · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.filter_eq', Finset.filter_or ];
          · rcases i with ( _ | _ | i ) <;> simp_all +decide [ Finset.filter_eq, Finset.filter_or, Finset.filter_and ];
            · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Finset.filter_eq', Finset.filter_ne' ];
            · rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ Finset.filter_eq', Finset.filter_ne' ];
            · split_ifs <;> simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
              any_goals omega;
              · grind;
              · subst_vars; simp +arith +decide [ Finset.filter_eq', Finset.filter_ne' ] ;
      · rcases i with ⟨ _ | i, hi ⟩ <;> norm_num at *;
        rcases lt_or_eq_of_le ( Nat.le_of_lt_succ ( by linarith : i < n + 2 ) ) with h | rfl <;> simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
        · grind +splitIndPred;
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num;
          use ⟨ n + 1, by linarith ⟩ ; ext ; aesop

lemma one_ne_zero_fin (n : ℕ) (h0 : ¬n = 0) :
    (fun _ : Fin (n + 1) => (1 : ℤ)) ≠ 0 := by
      -- The vector of all ones is not the zero vector because 1 is not equal to 0.
      simp [funext_iff]

theorem det_a'C (n : ℕ) (h0 : ¬n = 0) (h1 : ¬n = 1) :
    (a'C n).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨fun _ => 1, one_ne_zero_fin n h0, a'C_mulVec_one n h0 h1⟩
