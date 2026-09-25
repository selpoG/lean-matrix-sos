/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.RationalFunction.CommonDenominator
import MatrixSOS.Proof.FullLineAlgebra.SquareExtension

/-!
# Clearing denominators in full-line matrix factorizations
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS
theorem mapEval_squareExtension_posSemidef
    {m : ℕ}
    (P : PolyMat m)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∀ x : ℝ, (mapEval x (squareExtension P)).PosSemidef := by
  simpa [squareExtension] using mapEval_fromBlocks_det_posSemidef P hP

/--
Clears a common denominator from a rational square factorization
`A = S.transpose * S`.
-/
theorem scaled_square_eq_of_rat_factorization_of_common_denominator
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι Poly)
    {S : Matrix ι ι FracPoly}
    (hS : mapToFrac A = S.transpose * S)
    {q : Poly}
    {T : Matrix ι ι Poly}
    (hT : (algebraMap Poly FracPoly q) • S = mapToFrac T) :
    (q ^ 2) • A = T.transpose * T := by
  apply (mapToFrac_inj).mp
  calc
    mapToFrac ((q ^ 2) • A)
        = (algebraMap Poly FracPoly (q ^ 2)) • mapToFrac A := by
            ext i j
            simp [mapToFrac]
    _ = ((algebraMap Poly FracPoly q) ^ 2) • mapToFrac A := by
            simp
    _ = ((algebraMap Poly FracPoly q) * (algebraMap Poly FracPoly q)) • mapToFrac A := by
            simp [pow_two]
    _ = (algebraMap Poly FracPoly q) •
          ((algebraMap Poly FracPoly q) • mapToFrac A) := by
            rw [smul_smul]
    _ = (algebraMap Poly FracPoly q) •
          ((algebraMap Poly FracPoly q) • (S.transpose * S)) := by rw [hS]
    _ = ((algebraMap Poly FracPoly q) • S).transpose *
          ((algebraMap Poly FracPoly q) • S) := by
            rw [transpose_smul]
            rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (mapToFrac T).transpose * mapToFrac T := by rw [hT]
    _ = mapToFrac (T.transpose * T) := by
          symm
          rw [mapToFrac_mul, mapToFrac_transpose]

/--
Denominator clearing for rational matrix square factorizations.
-/
theorem exists_scaled_poly_matrix_square_of_rat_factorization
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι Poly)
    {S : Matrix ι ι FracPoly}
    (hS : mapToFrac A = S.transpose * S) :
    ∃ q : Poly, q ≠ 0 ∧
      ∃ T : Matrix ι ι Poly, (q ^ 2) • A = T.transpose * T := by
  rcases exists_poly_matrix_of_mul_common_denominator_matrix S with ⟨q, hq, T, hT⟩
  exact ⟨q, nonZeroDivisors.ne_zero hq, T,
    scaled_square_eq_of_rat_factorization_of_common_denominator A hS hT⟩

end MatrixSOS
