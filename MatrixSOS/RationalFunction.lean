/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Polynomial
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational functions and positivity away from poles
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

abbrev FracPoly := FractionRing Poly

/-- Ordered-field condition used by the positivity witness: every nonnegative element is a square. -/
class NonnegSquareClosed (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Prop where
  isSquare_of_nonneg : ∀ {x : K}, 0 ≤ x → IsSquare x

def mapToFrac {ι κ : Type*} (A : Matrix ι κ Poly) : Matrix ι κ FracPoly :=
  A.map (algebraMap Poly FracPoly)

/-- A concrete numerator/denominator representation of a rational polynomial. -/
def IsFracRep (r : FracPoly) (num den : Poly) : Prop :=
  den ≠ 0 ∧ r = algebraMap Poly FracPoly num / algebraMap Poly FracPoly den

/-- Scalar positivity predicate used by the rational binary boundary: `r` is nonnegative at every
real point where a polynomial representative is defined. -/
def RatNonnegWhereDefined (r : FracPoly) : Prop :=
  ∀ x : ℝ, ∀ {num den : Poly}, IsFracRep r num den → den.eval x ≠ 0 →
    0 ≤ num.eval x / den.eval x

/--
Binary rational-function boundary used by the diagonal reduction: if two
nonzero rational functions are nonnegative wherever defined on `ℝ`, then the
binary diagonal form `⟨a,b⟩` represents `1`.
-/
def FracBinaryRepresentsOneStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    RatNonnegWhereDefined a →
    RatNonnegWhereDefined b →
    ∃ u v : FracPoly, a * u ^ 2 + b * v ^ 2 = 1

end MatrixSOS
