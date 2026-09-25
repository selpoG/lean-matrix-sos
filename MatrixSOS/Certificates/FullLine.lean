/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.FullLine.Exact

/-!
# Public certificates for positivity on the real line
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

/--
The reverse direction of the full-line SOS theorem: a factorization
`P = R.transpose * R` gives pointwise positive semidefiniteness on the real
line.
-/
theorem fullLine_posSemidef_of_eq_transpose_mul
    {m ℓ : ℕ}
    (P : PolyMat m)
    (R : Matrix (Fin ℓ) (Fin m) (Polynomial ℝ))
    (hR : P = R.transpose * R) :
    ∀ x : ℝ, (mapEval x P).PosSemidef := by
  intro x
  subst P
  simpa using
    (Matrix.posSemidef_conjTranspose_mul_self (A := mapEval x R))

/--
Bounded full-line positive semidefiniteness iff bounded rectangular SOS
factorization.

The factor is rectangular: `R` has rows indexed by `Fin (m + 1)` and columns
indexed by `Fin m`.
-/
theorem fullLine_posSemidef_iff_sos
    {m d : ℕ}
    (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (hsymm : P.IsSymm) :
    (∀ x : ℝ, (mapEval x P).PosSemidef) ↔
    ∃ (R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)),
      (∀ i j, natDegree (R i j) ≤ d) ∧
      P = R.transpose * R := by
  constructor
  · exact fullLine_psd_factorization_pos P hdeg hsymm
  · rintro ⟨R, _hRdeg, hR⟩
    exact fullLine_posSemidef_of_eq_transpose_mul P R hR

/--
Bounded full-line Gram certificate over the monomial basis of degree at most
`d`.
-/
def FullLineGramCertificateBounded {m : ℕ} (d : ℕ) (P : PolyMat m) : Prop :=
  ∃ Y : Matrix (GramIdx d m) (GramIdx d m) ℝ,
    Y.PosSemidef ∧ P = GramTerm d m Y

/--
The reverse direction for full-line Gram certificates: a PSD real Gram matrix
over the monomial basis gives pointwise positive semidefiniteness.
-/
theorem fullLine_posSemidef_of_gramTerm
    {m d : ℕ}
    (Y : Matrix (GramIdx d m) (GramIdx d m) ℝ)
    (hY : Y.PosSemidef) :
    ∀ x : ℝ, (mapEval x (GramTerm d m Y)).PosSemidef := by
  rcases isMatrixSOS_gramTerm_of_posSemidef hY with ⟨ℓ, R, hR⟩
  exact fullLine_posSemidef_of_eq_transpose_mul (GramTerm d m Y) R hR

/--
Bounded full-line positive semidefiniteness iff bounded Gram certificate.
-/
theorem fullLine_posSemidef_iff_gram
    {m d : ℕ}
    (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (hsymm : P.IsSymm) :
    (∀ x : ℝ, (mapEval x P).PosSemidef) ↔
    FullLineGramCertificateBounded d P := by
  constructor
  · intro hP
    rcases (fullLine_posSemidef_iff_sos P hdeg hsymm).1 hP with
      ⟨R, hRdeg, hR⟩
    exact boundedMatrixSOS_to_gramTerm ⟨m + 1, R, hRdeg, hR⟩
  · rintro ⟨Y, hY, rfl⟩
    exact fullLine_posSemidef_of_gramTerm Y hY

end MatrixSOS
