/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.RationalFunction
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Statements for rational-function sum-of-squares certificates
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section


namespace MatrixSOS

def FracBinaryRepresentsOneSqAddSqStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    (∃ r s : FracPoly, a = r ^ 2 + s ^ 2) →
    (∃ r s : FracPoly, b = r ^ 2 + s ^ 2) →
    ∃ u v : FracPoly, a * u ^ 2 + b * v ^ 2 = 1

/-- Equivalent ternary-isotropy form of the rational hard statement. This is the quadratic-form shape
closest to the eventual Witt local-global input: for nonzero sum-of-two-squares `a, b`, the form
`⟨1, -a, -b⟩` has an isotropic vector whose first coordinate is nonzero. -/
def FracTernaryIsotropicSqAddSqStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    (∃ r s : FracPoly, a = r ^ 2 + s ^ 2) →
    (∃ r s : FracPoly, b = r ^ 2 + s ^ 2) →
    ∃ x y z : FracPoly, x ≠ 0 ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2

def FracTernaryIsotropicOverSquareClosedExtensions (a b : FracPoly) : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
      [Algebra FracPoly K],
    ∃ x y z : K, x ≠ 0 ∧
      x ^ 2 =
        algebraMap FracPoly K a * y ^ 2 + algebraMap FracPoly K b * z ^ 2

/-- Plain isotropy version of the local nonnegative-square-closed condition for the ternary form
`⟨1, -a, -b⟩`. This is closer to the standard Witt local-global input; in the regular case
`a, b ≠ 0`, the stronger first-coordinate-nonzero statement can be recovered afterwards by an
elementary explicit algebraic transformation. -/
def FracTernaryPlainIsotropicOverSquareClosedExtensions (a b : FracPoly) : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
      [Algebra FracPoly K],
    ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 =
        algebraMap FracPoly K a * y ^ 2 + algebraMap FracPoly K b * z ^ 2

def FracTernaryIsotropicSquareClosedLocalGlobalStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    FracTernaryPlainIsotropicOverSquareClosedExtensions a b →
    ∃ x y z : FracPoly, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2

def FracTernarySquareClosedLocalGlobalStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    FracTernaryIsotropicOverSquareClosedExtensions a b →
    ∃ x y z : FracPoly, x ≠ 0 ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2

def FracPfister2PlainIsotropicOverSquareClosedExtensions (a b : FracPoly) : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
      [Algebra FracPoly K],
    ∃ x y z w : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      x ^ 2 -
          algebraMap FracPoly K a * y ^ 2 -
          algebraMap FracPoly K b * z ^ 2 +
          algebraMap FracPoly K a * algebraMap FracPoly K b * w ^ 2 = 0

def FracCCDDPlainIsotropicOverSquareClosedExtensions (c d : FracPoly) : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
      [Algebra FracPoly K],
    ∃ x y z w : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      algebraMap FracPoly K c * x ^ 2 +
        algebraMap FracPoly K c * y ^ 2 +
        algebraMap FracPoly K d * z ^ 2 +
        algebraMap FracPoly K d * w ^ 2 = 0

def FracCCDDPlainIsotropicOverSquareClosedExtensionsSqAddSqStatement : Prop :=
  ∀ {c d : FracPoly},
    c ≠ 0 →
    d ≠ 0 →
    FracCCDDPlainIsotropicOverSquareClosedExtensions c d →
    ∃ u v : FracPoly, -c * d = u ^ 2 + v ^ 2

def FracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement : Prop :=
  ∀ {c d : FracPoly},
    c ≠ 0 →
    d ≠ 0 →
    FracCCDDPlainIsotropicOverSquareClosedExtensions c d →
    RatNonnegWhereDefined (-c * d)

def FracNegativeRealPointValueSquareClosedCounterexampleStatement : Prop :=
  ∀ {r : FracPoly} {x : ℝ} {num den : Poly},
    IsFracRep r num den →
    den.eval x ≠ 0 →
    num.eval x / den.eval x < 0 →
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (_ : NonnegSquareClosed K) (_ : Algebra FracPoly K),
      algebraMap FracPoly K r < 0

def FracNegativeRealPolyValueSquareClosedCounterexampleStatement : Prop :=
  ∀ {p : Poly} {x : ℝ},
    p.eval x < 0 →
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (_ : NonnegSquareClosed K) (_ : Algebra FracPoly K),
      algebraMap FracPoly K (algebraMap Poly FracPoly p) < 0

def FracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement : Prop :=
  ∀ {r : FracPoly},
    (∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
        [Algebra FracPoly K], 0 < algebraMap FracPoly K r) →
      RatNonnegWhereDefined r

end MatrixSOS
