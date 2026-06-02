import Mathlib.Data.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace CartanMatrix

open Matrix

variable (n : ℕ)

/-- The Cartan matrix of type \widetilde{A}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    ┌---------- o ------------┐
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def A_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (i.val = 0 ∧ j.val = n) ∨ (j.val = 0 ∧ i.val = n) ∨
            (i.val = n - 1 ∧ j.val = n) ∨ (j.val = n - 1 ∧ i.val = n) then -1
    else 0

/-
The all-ones vector is in the kernel of A_tilda when n ≥ 2.
-/
lemma A_tilda_mulVec_one (hn : 2 ≤ n) :
    (A_tilda n) *ᵥ (fun _ => (1 : ℤ)) = 0 := by
      -- By definition of $A_tilda$, we know that its rows sum to zero.
      have h_row_sum : ∀ i : Fin (n + 1), ∑ j : Fin (n + 1), (A_tilda n) i j = 0 := by
        intro i
        by_cases hi : i.val < n;
        · by_cases hi' : i.val = 0 <;> by_cases hi'' : i.val = n - 1 <;> simp_all +decide [ Fin.sum_univ_castSucc, A_tilda ];
          · omega;
          · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Fin.sum_univ_succ, A ];
            norm_num [ Fin.ext_iff ];
          · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Fin.ext_iff ];
            simp_all +decide [ Fin.castPred, A ];
            rw [ Finset.sum_ite ] ; norm_num [ Finset.filter_eq, Finset.filter_or ];
            rw [ Finset.sum_eq_single ⟨ n, by linarith ⟩ ] <;> norm_num;
            · grind;
            · simp_all +decide [ Fin.ext_iff ];
          · -- Since $i \neq 0$ and $i \neq n - 1$, the sum of the entries in the $i$-th row of $A_n$ is $-1 + 2 - 1 = 0$.
            have h_row_sum : ∑ j : Fin n, (A n) (i.castLT hi) j = 0 := by
              unfold A;
              simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_or ];
              rw [ Finset.card_eq_two.mpr ] ; norm_num;
              refine' ⟨ ⟨ i + 1, by omega ⟩, ⟨ i - 1, by omega ⟩, _, _ ⟩ <;> simp +decide [ Fin.ext_iff, Finset.ext_iff ];
              · omega;
              · grind;
            grind;
        · simp_all +decide [ Fin.eq_last_of_not_lt hi, A_tilda ];
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Fin.sum_univ_succ ];
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Fin.ext_iff, Fin.sum_univ_succ ];
          rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
          rw [ Finset.sum_ite ] ; norm_num;
          rw [ Finset.sum_eq_single ⟨ n, by linarith ⟩ ] <;> norm_num;
          · rw [ Finset.card_eq_one.mpr ] ; norm_num;
            exact ⟨ ⟨ n + 1, by linarith ⟩, by ext; aesop ⟩;
          · exact fun b hb₁ hb₂ => by contrapose! hb₂; exact Fin.ext hb₂;
      ext i; simp +decide [ *, Matrix.mulVec, dotProduct ] ;

theorem det_A_tilda : (A_tilda n).det =
    if n = 0 then 2
    else if n = 1 then 3
    else 0 := by
  by_cases h0 : n = 0
  · rw [h0]; simp [A_tilda]
  by_cases h1 : n = 1
  · rw [h1]; decide
  · simp [h0, h1]
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨fun _ => 1, by intro h; exact absurd (congr_fun h 0) one_ne_zero,
           A_tilda_mulVec_one n (by omega)⟩