/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Certificates.FullLine

/-!
# Certificates for constant positive semidefinite matrices
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

namespace Certificates

namespace Constant

/--
Constant matrix Gram factorization as the degree-zero full-line theorem.

A real matrix is positive semidefinite iff it is of the form
`R.transpose * R`, with a rectangular factor having `m + 1` rows.
-/
theorem posSemidef_iff_exists_gram
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    A.PosSemidef ↔
    ∃ R : Matrix (Fin (m + 1)) (Fin m) ℝ,
      A = R.transpose * R := by
  constructor
  · intro hA
    let P : PolyMat m := constPolyMat A
    have hdeg : ∀ i j, natDegree (P i j) ≤ 2 * 0 := by
      intro i j
      simp [P, constPolyMat]
    have hsymm : P.IsSymm := by
      refine Matrix.IsSymm.ext ?_
      intro i j
      have h := hA.isHermitian.apply i j
      simpa [P, constPolyMat] using h
    have hpos : ∀ x : ℝ, (mapEval x P).PosSemidef := by
      intro x
      simpa [P, mapEval_constPolyMat] using hA
    rcases (fullLine_posSemidef_iff_sos P hdeg hsymm).1 hpos with
      ⟨Rpoly, _hRdeg, hRpoly⟩
    refine ⟨mapEval 0 Rpoly, ?_⟩
    have hEval := congrArg (mapEval 0) hRpoly
    simpa [P, mapEval_constPolyMat, mapEval_mul, mapEval_transpose] using hEval
  · rintro ⟨R, rfl⟩
    simpa using (Matrix.posSemidef_conjTranspose_mul_self (A := R))

end Constant

end Certificates

end MatrixSOS
