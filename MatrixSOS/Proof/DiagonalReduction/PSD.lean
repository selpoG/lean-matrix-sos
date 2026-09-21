/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.Diagonal.Recursion
import MatrixSOS.Proof.DiagonalReduction.Bilinear.DiagonalData
import MatrixSOS.Proof.RationalFunction.BinarySum
import MatrixSOS.Proof.RationalFunction.NonnegWhereDefinedAlgebra

/-!
# Preservation of positive semidefiniteness under diagonal reduction
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem diagonal_det_eq_zero_of_entry_eq_zero
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (d : n → FracPoly)
    {i : n}
    (hi : d i = 0) :
    (Matrix.diagonal d).det = 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem diagonal_entry_ne_zero_of_det_ne_zero
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (d : n → FracPoly)
    (hdet : (Matrix.diagonal d).det ≠ 0) :
    ∀ i, d i ≠ 0 := by
  intro i hi
  exact hdet (diagonal_det_eq_zero_of_entry_eq_zero d hi)

theorem exists_rat_factorization_of_real_psd_with_frac_det_square_det_ne_zero
    {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (hdet0 : (mapToFrac A).det ≠ 0)
    (hdet : ∃ r : FracPoly, (mapToFrac A).det = r ^ 2) :
    ∃ S : Matrix n n FracPoly,
      mapToFrac A = S.transpose * S := by
  rcases exists_orthogonal_basis_nonneg_diagonal_data_of_real_psd_with_frac_det_square
      A hA hdet with
    ⟨b, d, r, hdiag, hdiagdet, hnonneg⟩
  have htoMatrixDet0 :
      (LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (mapToFrac A))).det ≠ 0 := by
    have hnondeg : (Matrix.toBilin' (mapToFrac A)).Nondegenerate :=
      LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' (mapToFrac A) hdet0
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnondeg
  have hdiagdet0 : (Matrix.diagonal d).det ≠ 0 := by
    simpa [hdiag] using htoMatrixDet0
  have hne : ∀ i, d i ≠ 0 :=
    diagonal_entry_ne_zero_of_det_ne_zero d hdiagdet0
  rcases exists_rat_factorization_of_nonneg_diagonal_with_square_det_of_forall_ne_zero
      fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
      (fun ha hb => ratNonnegWhereDefined_mul ha hb)
      d hnonneg hne ⟨r, hdiagdet⟩ with
    ⟨R, hR⟩
  exact exists_rat_factorization_of_toBilin'_toMatrix_eq
    (A := mapToFrac A) b R (hdiag.trans hR)

end MatrixSOS
