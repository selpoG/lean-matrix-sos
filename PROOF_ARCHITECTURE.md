# Proof Architecture

[日本語版](PROOF_ARCHITECTURE.ja.md)

This note describes the proof strategy and module dependencies of
`lean-matrix-sos`.

## Main Theorem

The main theorem is the full-line matrix SOS factorization:

```lean
MatrixSOS.fullLine_posSemidef_iff_sos
```

It states that a real symmetric matrix polynomial `P : PolyMat m`, with entry
degrees at most `2 * d`, has a bounded polynomial factorization

```text
P = R.transpose * R
```

whenever `P(x)` is positive semidefinite for every real `x`.
The factor `R` is rectangular:

```lean
R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)
```

The endpoint-parametrized half-line Markov-Lukacs-type SOS certificate is a
corollary:

```lean
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
```

It first proves the normalized `[0, ∞)` certificate internally by applying the
full-line result to `M(t^2)` and splitting the factor into even and odd parts.
The public theorem exposes the endpoint-parametrized form `[a, ∞)` via affine
pullback.

## Proof Strategy

The proof route is:

```text
complex function field/Pfister source
  + rational-exponent Hahn nonnegative-square source
  -> binary sum-of-squares lemma over ℝ(X)
  + common denominators and irreducible-factor descent
  -> full-line polynomial matrix factorization
  -> parity split
  -> normalized half-line Markov-Lukacs-type SOS certificate
  -> half-line and finite-interval certificates
  -> optional Gram repackaging
```

The local-global endpoint is formulated for ordered extensions in which every
nonnegative element is a square.
The matrix factorization part depends on the Hahn/Tsen/Pfister material only
through the binary rational-function boundary
`MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined`, which
states that nonzero rational functions nonnegative at all real points where
defined satisfy `1 = a * u^2 + b * v^2` for suitable `u, v : ℝ(X)`.

```lean
theorem fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
```

## Rational-Exponent Hahn Source

The file `MatrixSOS/Proof/RationalHahn.lean` defines the
lexicographically ordered Hahn field with real coefficients and rational value
group:

```lean
abbrev RationalHahnField := Lex (HahnSeries ℚ ℝ)
```

and proves:

```lean
theorem rationalHahnNonnegSquareStatement :
    forall {x : RationalHahnField}, 0 <= x -> IsSquare x
```

The proof separates a nonzero Hahn series into its leading monomial and a unit
with positive-order error term. The leading coefficient is square-rooted in
`ℝ`; the rational exponent group `ℚ` allows halving the leading exponent; and
the unit square root is constructed with Mathlib's Hahn-series binomial family.

This is the only Hahn-series fact needed by the maintained spine.

## Tsen And Complex Function Field/Pfister Source

The projective common-zero theorem uses the commutative-algebra height input in
`MatrixSOS/Proof/ProjectiveIdealHeight.lean`.  The complex function field and
Pfister side lives under `MatrixSOS/Proof/ComplexFunctionField`.  It supplies
the Pfister-style isotropy input used by the nonnegative-square-closed
local-global endpoint. The matrix SOS proof consumes this side through the
rational-function boundary below. The standalone Tsen statements are exposed in
`MatrixSOS/Proof/Tsen.lean`.

## Rational-Function Boundary

The matrix SOS proof crosses from the ordered-field and Pfister material into
diagonal matrix reduction through one file:

```text
MatrixSOS/Proof/RationalFunction/BinarySum.lean
```

Its endpoint is:

```lean
theorem fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
```

Downstream files should depend on this endpoint, or on a theorem explicitly
parametrized by `FracBinaryRepresentsOneStatement`, rather than importing the
Hahn, Tsen, or Pfister proof modules directly.

## Irreducible-Factor Descent

The full-line factorization proof clears common denominators and then removes
irreducible denominator factors directly at the polynomial level. The relevant
files are grouped under:

```text
MatrixSOS/Proof/DiagonalReduction
MatrixSOS/Proof/NoRealRootDescent
MatrixSOS/Proof/FullLineAlgebra
MatrixSOS/Proof/FullLine
```

`DiagonalReduction` contains the rational-function diagonal factorization route,
including bilinear-form diagonalization and the Smith-kernel compression used in
the determinant-zero branch. `NoRealRootDescent` contains the polynomial block cancellation for
irreducible quadratic factors with no real root; real-root factors are handled
directly in `FullLine/Irreducible.lean`. `FullLineAlgebra` contains
common-denominator clearing, square-extension, and rectangular extraction.
`FullLine` assembles these pieces into the exact polynomial matrix
factorization.
The bounded full-line theorem is uniform in the degree parameter: the exact
factorization is independent of `d`, and the degree bound is extracted from the
diagonal entries of `P = R.transpose * R`.

## Certificates

The full-line certificate layer is under `MatrixSOS/Certificates/FullLine*.lean`.
Constant-matrix corollaries are kept separately in
`MatrixSOS/Certificates/Constant.lean`.
The normalized half-line layer in
`MatrixSOS/Proof/HalfLine.lean` is a proof-side step for the
public endpoint-parametrized half-line certificates in
`MatrixSOS/Certificates/HalfLine.lean`.
For finite intervals, `MatrixSOS/Proof/Interval/Certificates.lean` contains
the certificate predicates, `MatrixSOS/Proof/Interval/Normalized.lean`
contains the proof-side normalized `[0, 1]` construction, and
`MatrixSOS/Certificates/Interval.lean` exposes the endpoint-parametrized
`[a, b]` API.

The stable public APIs are:

```lean
MatrixSOS.fullLine_posSemidef_iff_sos
MatrixSOS.fullLine_posSemidef_iff_gram
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_affinePullback_iff
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd
MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

Half-line APIs expose direct Markov-Lukacs-type certificates in the
original variable.  The right half-line uses `M = S0 + (X - a) • S1`; the
left half-line uses `M = S0 + (a - X) • S1`.  Internally these statements are
proved by normalizing with affine pullbacks, but the public API states the
degree bound on `M` itself.
The finite interval API likewise exposes direct Markov-Lukacs-type certificates.
For entry degree bound `2 * d` it uses
`M = S0 + (X - a) * (b - X) • S1`; for entry degree bound `2 * d + 1` it uses
`M = (X - a) • S0 + (b - X) • S1`.  In the even case the factor degrees are
bounded by `d` for `S0` and by the natural predecessor of `d` for `S1`; in the
odd case both factor degree bounds are `d`.  As in the full-line and half-line
APIs, each bounded SOS component can be repackaged as a real positive
semidefinite Gram matrix by `MatrixSOS.boundedMatrixSOS_to_gramTerm`.
The proof normalizes `[a, b]` to `[0, 1]`,
applies the half-line route to the chart `x = u / (1 + u)`, dehomogenizes the
resulting SOS factorization, and then pulls the certificate back to the
original interval.  In the odd case the apparent extra degree in the first
half-line factor is removed by taking the top coefficient of the diagonal
entries of the equality and using that a finite sum of real squares is zero
only when each summand is zero.

The scalar corollary specializes the full-line theorem to `m = 1` and exposes
the result directly as `p = q ^ 2 + r ^ 2`.  The constant corollary is the
degree-zero edge case: a real positive semidefinite matrix is exactly a
rectangular Gram matrix `R.transpose * R`, with the same `m + 1` fixed row count as
the full-line theorem.

## Edge Cases

The maintained statements are uniform in `m : Nat` and `d : Nat`.
In particular:

- `d = 0` is handled by the same full-line factorization theorem and the
  final diagonal-entry degree estimate; no separate public zero-degree branch
  is needed.
- `m = 0` is covered by the same polymorphic statements, with matrix index
  type `Fin 0`.
- The zero matrix is handled by the same exact factorization and degree
  extraction route.
- Singular matrix polynomials are included: the public theorem assumes
  symmetry and pointwise positive semidefiniteness, not regularity or
  nonzero determinant.
- Odd entry degrees are allowed syntactically; the theorem only requires the
  stated entry bound `natDegree (P i j) <= 2 * d`.

## Verification

Use the following commands for routine checks:

```bash
lake build MatrixSOS.Certificates
lake build MatrixSOS
```

For a local axiom audit, run:

```lean
#print axioms MatrixSOS.fullLine_posSemidef_iff_sos
#print axioms MatrixSOS.fullLine_posSemidef_iff_gram
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
#print axioms MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
#print axioms MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

Documentation-only changes do not require rebuilding Lean.
