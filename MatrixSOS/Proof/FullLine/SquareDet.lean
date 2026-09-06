/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.FullLine.Irreducible
import MatrixSOS.Proof.DiagonalReduction.PSD
import MatrixSOS.Proof.FullLineAlgebra.Denominators

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem polynomial_square_factor_of_real_psd_with_poly_square_det
    {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (hdet0 : A.det ≠ 0)
    {r : Poly}
    (hdet : A.det = r ^ 2) :
    ∃ U : Matrix n n Poly,
      A = U.transpose * U := by
  rcases exists_rat_factorization_of_real_psd_with_frac_det_square_det_ne_zero
      A hA
      (by
        rw [← mapToFrac_det]
        exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hdet0)
      ⟨algebraMap Poly FracPoly r, by
        calc
          (mapToFrac A).det = algebraMap Poly FracPoly A.det := by
            symm
            exact mapToFrac_det A
          _ = algebraMap Poly FracPoly (r ^ 2) := by rw [hdet]
          _ = (algebraMap Poly FracPoly r) ^ 2 := by simp⟩ with
    ⟨S, hS⟩
  rcases exists_scaled_poly_matrix_square_of_rat_factorization A hS with ⟨q, hq, T, hT⟩
  exact polynomial_square_factor_of_scaled_square_ne_zero A hq hT

theorem polynomial_square_factor_of_squareExtension
    {m : ℕ}
    (P : PolyMat m)
    (hdet0 : P.det ≠ 0)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∃ S : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) Poly,
      squareExtension P = S.transpose * S := by
  exact polynomial_square_factor_of_real_psd_with_poly_square_det
    (squareExtension P)
    (mapEval_squareExtension_posSemidef P hP)
    (by
      rw [det_squareExtension]
      exact pow_ne_zero 2 hdet0)
    (det_squareExtension P)


end MatrixSOS
