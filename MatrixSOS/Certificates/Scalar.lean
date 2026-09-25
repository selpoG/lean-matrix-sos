/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Certificates.FullLine

/-!
# Scalar polynomial sum-of-squares certificates
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

/--
A real polynomial is a bounded sum of two polynomial squares, with both square
factors of degree at most `d`.
-/
def IsPolynomialSOSBounded (d : ℕ) (p : Poly) : Prop :=
  ∃ q r : Poly, natDegree q ≤ d ∧ natDegree r ≤ d ∧ p = q ^ 2 + r ^ 2

/-- The `1 × 1` matrix polynomial whose unique entry is `p`. -/
def scalarPolyMat (p : Poly) : PolyMat 1 :=
  fun _ _ => p

lemma scalarPolyMat_isSymm (p : Poly) :
    (scalarPolyMat p).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  fin_cases i
  fin_cases j
  rfl

lemma scalarPolyMat_posSemidef_of_nonneg {p : Poly}
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∀ x : ℝ, (mapEval x (scalarPolyMat p)).PosSemidef := by
  intro x
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    fin_cases i
    fin_cases j
    simp [mapEval, scalarPolyMat]
  · intro v
    have hv : ∀ i : Fin 1, v i = v 0 := by
      intro i
      fin_cases i
      rfl
    have hs : 0 ≤ (v 0) ^ 2 * p.eval x :=
      mul_nonneg (sq_nonneg (v 0)) (hp x)
    simpa [mapEval, scalarPolyMat, Matrix.mulVec, dotProduct, hv, pow_two,
      mul_assoc, mul_comm, mul_left_comm] using hs

namespace Certificates

namespace Scalar

/--
Bounded scalar univariate SOS theorem as a corollary of the full-line matrix
theorem: a real polynomial of degree at most `2 * d` is nonnegative on the real
line iff it is a sum of two polynomial squares of degree at most `d`.
-/
theorem polynomial_nonnegOn_univ_iff_sos {d : ℕ} (p : Poly)
    (hdeg : natDegree p ≤ 2 * d) :
    (∀ x : ℝ, 0 ≤ p.eval x) ↔ IsPolynomialSOSBounded d p := by
  constructor
  · intro hp
    have hmatDeg : ∀ i j, natDegree (scalarPolyMat p i j) ≤ 2 * d := by
      intro i j
      fin_cases i
      fin_cases j
      simpa [scalarPolyMat] using hdeg
    rcases (fullLine_posSemidef_iff_sos
        (scalarPolyMat p) hmatDeg (scalarPolyMat_isSymm p)).1
        (scalarPolyMat_posSemidef_of_nonneg hp) with
      ⟨R, hRdeg, hR⟩
    refine ⟨R 0 0, R 1 0, hRdeg 0 0, hRdeg 1 0, ?_⟩
    have hentry := congrArg (fun M : PolyMat 1 => M 0 0) hR
    simpa [scalarPolyMat, Matrix.mul_apply, pow_two, add_comm, add_left_comm, add_assoc] using
      hentry
  · rintro ⟨q, r, _hqdeg, _hrdeg, rfl⟩ x
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_pow]
    exact add_nonneg (sq_nonneg (q.eval x)) (sq_nonneg (r.eval x))

end Scalar

end Certificates

end MatrixSOS
