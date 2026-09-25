/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS
import MatrixSOS.Proof.Tsen

/-!
# Small public API examples

This file is not part of the proof spine.  It is a lightweight usability test
for the public theorem statements.
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS.Examples

example (K : Type) [Field K] [IsAlgClosed K] :
    ProjectiveHomogeneousDimensionStatement K :=
  MatrixSOS.algebraicallyClosed_commonZero_of_homogeneous K

example (K : Type) [Field K] [IsAlgClosed K] :
    C1FieldStatement (RatFunc K) :=
  MatrixSOS.Tsen.algebraicallyClosed_ratFunc_c1FieldStatement K

example {m d : ℕ} (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (hsymm : P.IsSymm)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∃ R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ),
      (∀ i j, natDegree (R i j) ≤ d) ∧ P = R.transpose * R :=
  (MatrixSOS.fullLine_posSemidef_iff_sos P hdeg hsymm).1 hP

example {m d : ℕ} (P : PolyMat m)
    (hdeg : ∀ i j, natDegree (P i j) ≤ 2 * d)
    (hsymm : P.IsSymm) :
    (∀ x : ℝ, (mapEval x P).PosSemidef) ↔
      FullLineGramCertificateBounded d P :=
  MatrixSOS.fullLine_posSemidef_iff_gram P hdeg hsymm

example {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciSOSCertificateBounded d a M :=
  MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
    a M hdeg hsymm

example {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciGramCertificateBounded d a M :=
  MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
    a M hdeg hsymm

example {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d)
    (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsGramCertificateBoundedEven d a b M :=
  MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
    hab M hdeg hsymm

example {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d)
    (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsCertificateBoundedEven d a b M :=
  MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
    hab M hdeg hsymm

example {d : ℕ} {p : Polynomial ℝ} (hdeg : natDegree p ≤ 2 * d) :
    (∀ x : ℝ, 0 ≤ p.eval x) ↔
      MatrixSOS.IsPolynomialSOSBounded d p :=
  MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos p hdeg

example {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b) :
    ∃ u v : FracPoly, a * u ^ 2 + b * v ^ 2 = 1 :=
  MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
    ha0 hb0 ha hb

end MatrixSOS.Examples
