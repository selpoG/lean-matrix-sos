/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS
import MatrixSOS.Proof.Tsen

/-!
# Public theorem audit

This file records reproducible checks for the public theorem surface.
Run it with:

```bash
lake env lean MatrixSOS/Audit.lean
```

The `#guard_msgs` checks enforce Lean/mathlib's standard classical axiom set
for these theorems: `propext`, `Classical.choice`, and
`Quot.sound`.
-/

/--
info: 'MatrixSOS.fullLine_posSemidef_iff_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MatrixSOS.fullLine_posSemidef_iff_sos

/--
info: 'MatrixSOS.fullLine_posSemidef_iff_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.fullLine_posSemidef_iff_gram

/--
info: 'MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos

/--
info: 'MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram

/--
info: 'MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos

/--
info: 'MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram

/--
info: 'MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even

/--
info: 'MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd

/--
info: 'MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even

/--
info: 'MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd

/--
info: 'MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos

/--
info: 'MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram

/--
info: 'MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined

/--
info: 'MatrixSOS.algebraicallyClosed_commonZero_of_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.algebraicallyClosed_commonZero_of_homogeneous

/--
info: 'MatrixSOS.Tsen.algebraicallyClosed_ratFunc_c1FieldStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixSOS.Tsen.algebraicallyClosed_ratFunc_c1FieldStatement

/--
info: MatrixSOS.fullLine_posSemidef_iff_sos {m d : ℕ} (P : MatrixSOS.PolyMat m)
  (hdeg : ∀ (i j : Fin m), Polynomial.natDegree (P i j) ≤ 2 * d) (hsymm : Matrix.IsSymm P) :
  (∀ (x : ℝ), (MatrixSOS.mapEval x P).PosSemidef) ↔
    ∃ R, (∀ (i : Fin (m + 1)) (j : Fin m), (R i j).natDegree ≤ d) ∧ P = R.transpose * R
-/
#guard_msgs in
#check MatrixSOS.fullLine_posSemidef_iff_sos

#check MatrixSOS.fullLine_posSemidef_iff_gram
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd
#check MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
#check MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
#check MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
#check MatrixSOS.algebraicallyClosed_commonZero_of_homogeneous
#check MatrixSOS.Tsen.algebraicallyClosed_ratFunc_c1FieldStatement
