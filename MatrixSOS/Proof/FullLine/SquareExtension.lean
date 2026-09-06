/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.FullLine.SquareDet
import MatrixSOS.Proof.Polynomial
import Mathlib.LinearAlgebra.StdBasis

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem natDegree_le_of_rect_factorization
    {m d ℓ : ℕ}
    (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (hR : P = R.transpose * R) :
    ∀ i j, natDegree (R i j) ≤ d := by
  intro i j
  have hdiag :
      P j j = ∑ a, (R a j) ^ 2 := by
    rw [hR]
    simp [Matrix.mul_apply, pow_two]
  have hdegDiag : natDegree (∑ a, (R a j) ^ 2) ≤ 2 * d := by
    simpa [hdiag] using hdeg j j
  exact natDegree_le_of_sum_squares (f := fun a : Fin ℓ => R a j) hdegDiag i

theorem basis_card_eq
    {m o : ℕ}
    (b : Module.Basis (Fin o) Poly (Fin m → Poly)) :
    o = m := by
  have hb : Module.finrank Poly (Fin m → Poly) = o := by
    simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis b)
  have hstd : Module.finrank Poly (Fin m → Poly) = m := by
    calc
      Module.finrank Poly (Fin m → Poly) = Fintype.card (Fin m) :=
        Module.finrank_eq_card_basis (Pi.basisFun Poly (Fin m))
      _ = m := Fintype.card_fin m
  omega

theorem fullLine_psd_square_extension_exact
    {m : ℕ}
    (P : PolyMat m)
    (hdet0 : P.det ≠ 0)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∃ S : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) Poly,
      squareExtension P = S.transpose * S := by
  exact polynomial_square_factor_of_squareExtension P hdet0 hP

end MatrixSOS
