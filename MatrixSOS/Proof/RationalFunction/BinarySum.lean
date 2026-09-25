/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.RationalFunction.BinarySumProof

/-!
Single rational-function boundary used by the matrix SOS proof.

The downstream diagonal and full-line arguments only need
`fracPoly_binaryForm_represents_one_of_nonnegWhereDefined`, the binary
sum-of-squares representation over `ℝ(X)`, plus the definitions used in its
statement.  The Hahn, Tsen, Pfister, and nonnegative-square-closed proof code
is separated in
`MatrixSOS.Proof.RationalFunction.BinarySumProof`.

Mechanically replacing the binary rational-function proof by an assumed input
should require replacing this file by the same imports from `Definitions` plus
an assumed theorem for
`fracPoly_binaryForm_represents_one_of_nonnegWhereDefined`.
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

/--
Binary representation theorem over `ℝ(X)`.

If two nonzero rational functions are nonnegative at every real point where
they are defined, then the diagonal binary form `⟨a,b⟩` represents `1`.
-/
theorem fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b) :
    ∃ u v : FracPoly, a * u ^ 2 + b * v ^ 2 = 1 :=
  fracBinaryRepresentsOne_proof ha0 hb0 ha hb

end MatrixSOS
