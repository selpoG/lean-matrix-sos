/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.FullLine.SquareExtension
import MatrixSOS.Proof.DiagonalReduction.Bilinear.MatrixBridge
import MatrixSOS.Proof.DiagonalReduction.Compression.ZeroRow

/-!
# Exact full-line matrix sum-of-squares certificates
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

private def padRowsSum {α : Type*} [Zero α] {r n c : ℕ}
    (R : Matrix (Fin r) (Fin c) α) : Matrix (Fin r ⊕ Fin n) (Fin c) α :=
  Sum.elim R (0 : Matrix (Fin n) (Fin c) α)

private def padRowsTo {α : Type*} [Zero α] {r n c : ℕ}
    (h : r ≤ n) (R : Matrix (Fin r) (Fin c) α) : Matrix (Fin n) (Fin c) α :=
  Matrix.reindex
    ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))) : Fin r ⊕ Fin (n - r) ≃ Fin n)
    (Equiv.refl (Fin c))
    (padRowsSum (n := n - r) R)

private theorem padRowsSum_transpose_mul
    {α : Type*} [CommSemiring α] {r n c : ℕ}
    (R : Matrix (Fin r) (Fin c) α) :
    (padRowsSum (n := n) R).transpose * padRowsSum (n := n) R = R.transpose * R := by
  change
    (Matrix.fromRows R (0 : Matrix (Fin n) (Fin c) α)).transpose *
        Matrix.fromRows R 0 =
      R.transpose * R
  have hcols :
      (Matrix.fromRows R (0 : Matrix (Fin n) (Fin c) α)).transpose =
        Matrix.fromCols R.transpose (0 : Matrix (Fin c) (Fin n) α) := by
    simpa using (Matrix.transpose_fromRows R (0 : Matrix (Fin n) (Fin c) α))
  calc
    (Matrix.fromRows R (0 : Matrix (Fin n) (Fin c) α)).transpose * Matrix.fromRows R 0 =
      Matrix.fromCols R.transpose (0 : Matrix (Fin c) (Fin n) α) *
        Matrix.fromRows R 0 := by rw [hcols]
    _ = R.transpose * R := by
      simpa using
        (Matrix.fromCols_mul_fromRows R.transpose
          (0 : Matrix (Fin c) (Fin n) α) R (0 : Matrix (Fin n) (Fin c) α))

private theorem padRowsTo_transpose_mul
    {α : Type*} [CommSemiring α] {r n c : ℕ}
    (h : r ≤ n) (R : Matrix (Fin r) (Fin c) α) :
    (padRowsTo h R).transpose * padRowsTo h R = R.transpose * R := by
  unfold padRowsTo
  rw [transpose_mul_reindex_rows_eq]
  exact padRowsSum_transpose_mul (n := n - r) R

theorem fullLine_psd_factorization_exact :
    ∀ m : ℕ,
      ∀ P : PolyMat m,
        P.IsSymm →
        (∀ x : ℝ, (mapEval x P).PosSemidef) →
        ∃ R : Matrix (Fin (m + 1)) (Fin m) Poly,
          P = R.transpose * R
  | 0, P, hsymm, hP => by
      refine ⟨0, ?_⟩
      ext i
      exact Fin.elim0 i
  | m + 1, P, hsymm, hP => by
      by_cases hdet : P.det = 0
      · rcases exists_basis_index_toMatrix_zero_row_col_of_det_eq_zero P hsymm hdet with
          ⟨o, b, i0, hrow, hcol⟩
        have ho : o = m + 1 := basis_card_eq b
        subst ho
        let B : PolyMat (m + 1) := LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P)
        have hsymmB : B.IsSymm := bilinOfPolyMat_toMatrix_isSymm P hsymm b
        have hPB : ∀ x : ℝ, (mapEval x B).PosSemidef :=
          mapEval_bilinOfPolyMat_toMatrix_posSemidef P b hP
        rcases
            fullLine_psd_factorization_exact m (compressPolyMat i0 B)
              (compressPolyMat_isSymm hsymmB)
              (fun x => compressPolyMat_posSemidef x (hPB x)) with
          ⟨R, hR⟩
        rcases exists_fin_exact_factorization_of_compress_eq_and_zero_row_col
            i0 B hrow hcol R hR with
          ⟨R', hR'⟩
        rcases exists_factorization_of_bilinOfPolyMat_toMatrix_eq P b R' hR' with ⟨S, hS⟩
        refine ⟨padRowsTo (show m + 1 ≤ m + 2 by omega) S, ?_⟩
        rw [padRowsTo_transpose_mul]
        exact hS
      · rcases fullLine_psd_square_extension_exact P hdet hP with
          ⟨S, hS⟩
        rcases exists_fin_rectangular_factorization_of_squareExtension_eq_square P S hS with
          ⟨R, hR⟩
        exact ⟨R, hR⟩

theorem fullLine_psd_factorization_pos
    {m d : ℕ}
    (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (hsymm : P.IsSymm)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∃ (R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)),
      (∀ i j, natDegree (R i j) ≤ d) ∧
      P = R.transpose * R := by
  rcases fullLine_psd_factorization_exact m P hsymm hP with ⟨R, hR⟩
  exact ⟨R, natDegree_le_of_rect_factorization P hdeg R hR, hR⟩

end MatrixSOS
