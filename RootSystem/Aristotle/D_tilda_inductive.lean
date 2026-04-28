import Mathlib

open CartanMatrix
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

-- ============================================================
-- Reproduced definitions
-- ============================================================

/-- D_rev is D with reversed indices. -/
def DRev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

/-- The extended Cartan matrix D_tilda. -/
def DTilda (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (DRev n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 2 = i then -1
    else if (i : ℕ) + 2 = j then -1
    else 0

-- det(DRev n) = det(D n)
@[simp]
lemma det_DRev (n : ℕ) : det (DRev n) = det (D n) := by
  have h1 : DRev n = Matrix.of fun i j : Fin n ↦ D n (i.rev) (j.rev) := by
    ext i j; simp [DRev, D, Fin.rev]; split_ifs <;> grind
  rw [h1]
  have h2 : (Matrix.of fun i j : Fin n ↦ D n (i.rev) (j.rev)) =
    (reindex (Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective)
             (Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective)) (D n) := by
    ext i j; simp [reindex, Equiv.ofBijective, Function.surjInv]; grind
  simp [h2]

-- ============================================================
-- det(D n) = 4 for n ≥ 2: Using the indMatrix recurrence
-- ============================================================

/-- ind_matrix adds a row/column with distance-1 connections. -/
def indMatrix1 (Y : Matrix (Fin n) (Fin n) R) (a b : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then Y (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then a
    else if (i : ℕ) + 1 = j then b
    else 0

/-
DRev(n+2) = indMatrix1(DRev(n+1), -1, -1) for n ≥ 2.
    (Fails for n < 2 due to the branching at positions 0,1,2 in DRev.)
-/
lemma DRev_succ_eq_indMatrix1 (n : ℕ) (hn : n ≥ 2) :
    DRev (n + 1 + 1) = indMatrix1 (DRev (n + 1)) (-1) (-1) := by
  ext i j; simp +decide [ DRev, indMatrix1 ] ;
  rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num [ Fin.ext_iff ];
  · grind;
  · grind;
  · grind

/-- The top-left block of DRev(n+1) is DRev(n). -/
lemma topLeftBlock_DRev (n : ℕ) :
    (DRev (n + 1)).submatrix Fin.castSucc Fin.castSucc = DRev n := by
  ext i j; simp +decide [ DRev ] ;
  simp +decide [ Fin.ext_iff ]

/-
The distance-1 recurrence for determinants (general, not specific to DRev).
-/
lemma indDet1 (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (Z : Matrix (Fin n) (Fin n) R)
    (a b : R)
    (hY : Y.submatrix Fin.castSucc Fin.castSucc = Z) :
    (indMatrix1 Y a b).det = 2 * Y.det - a * b * Z.det := by
  rw [ ← hY, Matrix.det_succ_row _ ( Fin.last _ ) ];
  rw [ Fin.sum_univ_castSucc ];
  rw [ Finset.sum_eq_single ( Fin.last _ ) ] <;> simp +decide [ indMatrix1 ];
  · rw [ Matrix.det_succ_column _ ( Fin.last _ ) ];
    rw [ Finset.sum_eq_single ( Fin.last _ ) ] <;> simp +decide [ Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt ];
    · simp +decide [ Nat.succ_eq_add_one, Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero, Matrix.submatrix ];
      rw [ if_neg ( by linarith ) ] ; ring;
      congr;
      ext i j; simp +decide [ Fin.le_last ] ;
      grind;
    · grind;
  · grind

/-- DRev satisfies the recurrence det(DRev(n+2)) = 2*det(DRev(n+1)) - det(DRev(n))
    for n ≥ 2. -/
lemma det_DRev_recurrence (n : ℕ) (hn : n ≥ 2) :
    det (DRev (n + 2)) = 2 * det (DRev (n + 1)) - det (DRev n) := by
  rw [DRev_succ_eq_indMatrix1 n hn]
  rw [indDet1 (DRev (n + 1)) (DRev n) (-1) (-1) (topLeftBlock_DRev n)]
  ring

/-- det(D n) = 4 for n ≥ 2. -/
lemma det_D_ge2 (n : ℕ) (hn : n ≥ 2) : det (D n) = 4 := by
  rw [← det_DRev]
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 2, _ => native_decide
    | 3, _ => native_decide
    | 4, _ => native_decide
    | 5, _ => native_decide
    | n + 6, _ =>
      rw [show n + 6 = (n + 4) + 2 by omega]
      rw [det_DRev_recurrence (n + 4) (by omega)]
      have h1 := ih (n + 5) (by omega) (by omega)
      have h2 := ih (n + 4) (by omega) (by omega)
      simp [det_DRev] at h1 h2 ⊢
      linarith

-- ============================================================
-- ind_matrix2 (distance-2 off-diagonal connections)
-- ============================================================

/-- The matrix obtained by adding a row and a column to `Y`, with entries `a` and `b`
at distance 2 from the diagonal. -/
def indMatrix2 (Y : Matrix (Fin n) (Fin n) R) (a b : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then Y (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 2 = i then a
    else if (i : ℕ) + 2 = j then b
    else 0

-- ============================================================
-- DTilda = indMatrix2(DRev, -1, -1)
-- ============================================================

lemma DTilda_eq_indMatrix2 (n : ℕ) : DTilda n = indMatrix2 (DRev n) (-1) (-1) := by
  ext i j; simp [DTilda, indMatrix2]

/-
============================================================
The recurrence relation (indDet2)
============================================================

Step A: Double cofactor expansion of indMatrix2.
    det(indMatrix2 Y a b) = 2 * det(Y) - a * b * det(Y with row n and col n deleted)
-/
set_option maxHeartbeats 800000 in
lemma indDet2_cofactor {n : ℕ}
    (Y : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (a b : R) :
    (indMatrix2 Y a b).det =
      2 * Y.det - a * b *
        (Y.submatrix
          (Fin.succAbove ⟨n, by omega⟩)
          (Fin.succAbove ⟨n, by omega⟩)).det := by
  unfold indMatrix2; simp +decide [ Fin.ext_iff, Fin.val_add ];
  rw [ ← Matrix.det_transpose, Matrix.det_succ_row _ ( Fin.last _ ) ];
  rw [ Fin.sum_univ_castSucc ];
  simp +decide [ Fin.ext_iff, Matrix.submatrix, Matrix.transpose_apply ];
  rw [ Finset.sum_eq_single ⟨ n, by linarith ⟩ ] <;> simp +decide [ Fin.ext_iff, Fin.val_add ];
  · rw [ if_neg ( by linarith ) ];
    rw [ Matrix.det_succ_column _ ( Fin.last _ ) ];
    rw [ Finset.sum_eq_single ⟨ n, by linarith ⟩ ] <;> simp +decide [ Fin.ext_iff, Fin.val_add ];
    · simp +decide [ Fin.succAbove, Fin.castLT ];
      simp +decide [ Fin.lt_def, Fin.ext_iff, Matrix.submatrix ];
      rw [ if_neg ( by linarith ) ] ; ring;
      simp +decide [ Fin.succAbove, Matrix.det_apply' ];
      congr! 2;
      · refine' congr_arg _ ( Finset.sum_bij ( fun x _ => x⁻¹ ) _ _ _ _ ) <;> simp +decide [ Fin.ext_iff, Fin.val_add ];
        · exact fun b => ⟨ b⁻¹, inv_inv b ⟩;
        · intro σ; rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ Fin.ext_iff, Fin.val_add ] ;
          congr! 2;
          split_ifs <;> simp_all +decide [ Fin.ext_iff, Fin.val_add ];
          any_goals omega;
          · congr! 1;
          · congr! 1;
      · refine' Finset.sum_bij ( fun σ _ => σ⁻¹ ) _ _ _ _ <;> simp +decide;
        · exact fun b => ⟨ b⁻¹, inv_inv b ⟩;
        · intro a; rw [ ← Equiv.prod_comp a.symm ] ; simp +decide ;
    · simp +decide [ Fin.succAbove, Fin.castLT ];
      simp +decide [ Fin.lt_def, Fin.ext_iff ];
      grind;
  · grind +qlia

/-
Step B: Block diagonal determinant under disconnection conditions.
    Y with row n and col n deleted has block diagonal structure
    [Z  0; 0  Y(n+1,n+1)] when Y satisfies disconnection conditions.
-/
set_option maxHeartbeats 400000 in
lemma block_diag_det {n : ℕ}
    (Y : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (Z : Matrix (Fin n) (Fin n) R)
    (hY_row : ∀ i : Fin n, Y (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 1)) = 0)
    (hY_col : ∀ j : Fin n, Y (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc j)) = 0)
    (hZ : Z = Y.submatrix
      (Fin.castLE (by omega : n ≤ n + 2))
      (Fin.castLE (by omega : n ≤ n + 2))) :
    (Y.submatrix
      (Fin.succAbove ⟨n, by omega⟩)
      (Fin.succAbove ⟨n, by omega⟩)).det =
      Z.det * Y (Fin.last (n + 1)) (Fin.last (n + 1)) := by
  rw [ ← Matrix.det_transpose, Matrix.det_succ_row _ ( Fin.last _ ) ];
  simp +decide [ Fin.ext_iff, Matrix.submatrix, Matrix.transpose_apply ];
  rw [ Finset.sum_eq_single ( Fin.last n ) ] <;> simp +decide [ *, Fin.succAbove ];
  · simp +decide [ Fin.lt_def, mul_comm ];
    exact congr_arg _ ( Matrix.det_transpose _ );
  · intro b hb; split_ifs <;> simp_all +decide [ Fin.ext_iff, Fin.lt_def ] ;
    · specialize hY_row ⟨ b, by linarith ⟩ ; aesop;
    · exact False.elim ( hb ( le_antisymm ( Fin.is_le _ ) ‹_› ) )

/-- When Y is (n+2)×(n+2) and satisfies disconnection conditions,
the determinant of indMatrix2 Y a b satisfies a recurrence. -/
lemma indDet2 {n : ℕ}
    (Y : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (Z : Matrix (Fin n) (Fin n) R)
    (a b : R)
    (hY_row : ∀ i : Fin n, Y (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 1)) = 0)
    (hY_col : ∀ j : Fin n, Y (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc j)) = 0)
    (hZ : Z = Y.submatrix
      (Fin.castLE (by omega : n ≤ n + 2))
      (Fin.castLE (by omega : n ≤ n + 2))) :
    (indMatrix2 Y a b).det =
      2 * Y.det - a * b * Y (Fin.last (n + 1)) (Fin.last (n + 1)) * Z.det := by
  rw [indDet2_cofactor, block_diag_det Y Z hY_row hY_col hZ]
  ring

-- ============================================================
-- Disconnection conditions for DRev
-- ============================================================

lemma DRev_disconnected_row (n : ℕ) (hn : n ≥ 2) (i : Fin n) :
    DRev (n + 2) (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 1)) = 0 := by
  simp [DRev]; grind

lemma DRev_disconnected_col (n : ℕ) (hn : n ≥ 2) (j : Fin n) :
    DRev (n + 2) (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc j)) = 0 := by
  simp [DRev]; grind

-- ============================================================
-- Top-left block and diagonal
-- ============================================================

lemma DRev_top_left_block (n : ℕ) :
    (DRev (n + 2)).submatrix
      (Fin.castLE (by omega : n ≤ n + 2))
      (Fin.castLE (by omega : n ≤ n + 2)) = DRev n := by
  ext i j; simp [DRev, Fin.castLE]; grind

lemma DRev_last_diag (n : ℕ) :
    DRev (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) = 2 := by
  simp [DRev]

-- ============================================================
-- The inductive formula for det(DTilda)
-- ============================================================

lemma det_DTilda_formula (n : ℕ) (hn : n ≥ 2) :
    (DTilda (n + 2)).det = 2 * (DRev (n + 2)).det - 2 * (DRev n).det := by
  rw [DTilda_eq_indMatrix2]
  have h := indDet2 (DRev (n + 2)) (DRev n) (-1) (-1)
    (DRev_disconnected_row n hn)
    (DRev_disconnected_col n hn)
    (DRev_top_left_block n).symm
  rw [h, DRev_last_diag]
  ring

-- ============================================================
-- The inductive proof of det(DTilda) = 0
-- ============================================================

/-- Alternative inductive proof that det(DTilda n) = 0 for n ≥ 4,
    using cofactor expansion instead of the null vector approach. -/
theorem det_DTilda_inductive (n : ℕ) (hn : n ≥ 4) : (DTilda n).det = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  show (DTilda ((m + 2) + 2)).det = 0
  rw [det_DTilda_formula (m + 2) (by omega)]
  simp [det_DRev, det_D_ge2 _ (by omega : m + 2 + 2 ≥ 2),
        det_D_ge2 _ (by omega : m + 2 ≥ 2)]