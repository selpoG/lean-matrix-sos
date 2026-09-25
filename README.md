# lean-matrix-sos

[日本語版](README.ja.md)

This repository formalizes, in Lean 4, sums-of-squares factorization theorems
for real symmetric univariate matrix polynomials.

Here SOS means a representation as a finite sum of polynomial matrix squares,
equivalently a factorization

```text
P = R.transpose * R
```

for a possibly rectangular polynomial matrix `R`.  A bounded SOS factor can
also be repackaged as an equivalent real Gram-matrix certificate by expanding
the factor in a monomial basis.

The main theorem is the full-line matrix SOS factorization:

```lean
#check MatrixSOS.fullLine_posSemidef_iff_sos
```

For a real symmetric matrix polynomial `P : PolyMat m` with entry degrees at
most `2 * d`, this theorem identifies pointwise positive semidefiniteness on
the real line with the existence of a possibly rectangular polynomial matrix
`R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)`, whose entry
degrees are at most `d` and such that

```text
P = R.transpose * R.
```

Here `R` has `m` columns and `m + 1` rows.
By the general SOS-to-Gram conversion
`MatrixSOS.boundedMatrixSOS_to_gramTerm`, the bounded full-line factorization
can equivalently be written as a real positive semidefinite Gram matrix over
the monomial basis of degree at most `d`.  This is also exposed directly:

```lean
#check MatrixSOS.fullLine_posSemidef_iff_gram
```

Half-line theorems give endpoint-parametrized Markov-Lukacs-type SOS
certificates:

```lean
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram
```

The first SOS theorem identifies positive semidefiniteness on `[a, ∞)` with a
bounded weighted SOS representation in the original variable:

```text
M = S0 + (X - a) • S1
```

where `S0` and `S1` are SOS matrix polynomials, with the standard even/odd
factor degree bounds `evenPartDegreeBound d = d / 2` and
`oddPartDegreeBound d = (d - 1) / 2`.
This is the SOS-first statement;
the corresponding bounded Gram representation is obtained by applying the same
general SOS-to-Gram conversion to `S0` and `S1`.  The reflected version for
`(-∞, a]` uses the weight `a - X`.

Finite intervals have direct Markov-Lukacs-type SOS certificates.  As in the
half-line case, positivity is expressed using SOS terms weighted by polynomials
nonnegative on the domain.  The certificate shape depends on the parity of the
degree bound:

```lean
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd
```

For `a < b`, the even-degree statement uses the bound `natDegree (M i j) ≤
2 * d` and identifies positive semidefiniteness on `[a, b]` with SOS matrix
polynomials `S0` and `S1` such that

```text
M = S0 + (X - a) * (b - X) • S1.
```

Here the factor degrees in the SOS certificate for `S0` are bounded by `d`,
and those for `S1` are bounded by `max (d - 1) 0`.
Consequently, the even interval certificate can also be written in Gram form as
`M = GramTerm d m Y0 + (X - a) * (b - X) • GramTerm (max (d - 1) 0) m Y1`,
with positive semidefinite real Gram matrices.

The odd-degree statement uses the bound `natDegree (M i j) ≤ 2 * d + 1` and
uses the complementary Markov-Lukacs form

```text
M = (X - a) • S0 + (b - X) • S1.
```

Here the factor degrees in both SOS certificates are bounded by `d`.
Consequently, the odd interval certificate can also be written in Gram form as
`M = (X - a) • GramTerm d m Y0 + (b - X) • GramTerm d m Y1`, with positive
semidefinite real Gram matrices.

Two small but useful special cases are exposed as standalone corollaries:

```lean
#check MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
#check MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

The scalar theorem specializes the full-line result to a single real
polynomial.  In the bounded form, if `natDegree p ≤ 2 * d`, then `p` is
nonnegative on the real line iff it has the form `q ^ 2 + r ^ 2`, with
`natDegree q ≤ d` and `natDegree r ≤ d`.  The constant theorem states that a
real positive semidefinite matrix is exactly a rectangular Gram matrix
`R.transpose * R`, with `m + 1` rows.

The rational-function boundary used inside the proof is also public:

```lean
#check MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
```

It says that if nonzero `a b : ℝ(X)` are nonnegative at every real point where
they are defined, then the binary diagonal form `⟨a,b⟩` represents `1`,
equivalently `a * u^2 + b * v^2 = 1` for some `u v : ℝ(X)`.

## Build

This project uses Lean 4 and mathlib through Lake.

```bash
lake build
```

To prefetch the pinned mathlib build cache before building, run:

```bash
lake exe cache get
```

The public certificate API can also be built directly with:

```bash
lake build MatrixSOS.Certificates
lake build MatrixSOS
```

The public theorem audit and API examples can be checked with:

```bash
lake build MatrixSOS.Audit MatrixSOS.Examples
```

`MatrixSOS/Audit.lean` records reproducible `#print axioms`, `#check`, and
`#guard_msgs` checks for the public theorems.  The audited public theorems use
no project-specific axioms; the observed axiom set is the standard classical
Lean/mathlib set
`[propext, Classical.choice, Quot.sound]`.

The axiom checks fail if any audited theorem's dependencies differ from this set.

`MatrixSOS/Examples.lean` is a small API usability test showing direct use of
the full-line, half-line, finite-interval, and scalar theorem statements.

For a command-line source scan, run:

```bash
rg -n "^\s*(axiom|unsafe|set_option)\b|\b(sorry|admit)\b" MatrixSOS MatrixSOS.lean -S
```

Mathlib's text-based style linters can be run with:

```bash
lake exe lint-style MatrixSOS MatrixSOS.Audit MatrixSOS.Examples
```

The proof write-ups can be built with `go-task` / [Task](https://taskfile.dev/):

```bash
task pdf
```

This requires `uplatex` and `dvipdfmx`.

This produces:

- `docs/matrix_sos_proof_ja.pdf`
- `docs/matrix_sos_proof_en.pdf`

## Proof Route

The full-line theorem is proved from three ingredients.

1. A complex function field/Pfister reduction over rational functions.
2. A Hahn field with rational value group, used as a nonnegative-square-closed
   ordered extension.
3. Common-denominator clearing and irreducible-factor descent for exact
   polynomial matrix factorization.

The normalized half-line theorem follows by applying the full-line theorem to
`P(t) = M(t^2)` and splitting the resulting factor into even and odd parts.
Endpoint-parametrized half-lines are obtained from the normalized statement by
affine pullback.  The finite-interval certificates are obtained by normalizing
`[a, b]` to `[0, 1]`, passing through a half-line chart, and dehomogenizing the
resulting SOS identities.  Gram certificates are optional repackagings of the
bounded SOS factors.

## Role of the Rational Hahn Field

The active proof spine uses the field named `RationalHahnField` only through
the fact that every nonnegative element of this ordered Hahn field is a square.
Here `RationalHahnField` is the lexicographically ordered Hahn field with real
coefficients and rational value group:

```lean
RationalHahnField = Lex (HahnSeries ℚ ℝ)
```

In the displayed Lean type, `ℚ` is the exponent/value group and `ℝ` is the
coefficient field. The project proves the square-root property directly by
normalizing a Hahn series by its leading term and applying the binomial
square-root construction to the remaining unit.

The detailed module map is in `PROOF_ARCHITECTURE.md`.

## Repository Layout

- `MatrixSOS/Polynomial.lean`: basic notation for real univariate polynomials.
- `MatrixSOS/PolyMatrix.lean`: public matrix-polynomial definitions, SOS
  predicates, affine pullbacks, and Gram forms.
- `MatrixSOS/Proof/Polynomial`: scalar real-polynomial lemmas used by the
  rational-function and irreducible-factor descent parts.
- `MatrixSOS/Proof/RationalFunction`: rational-function positivity,
  local-global statements, and the binary sum-of-squares boundary used by the
  matrix proof.
- `MatrixSOS/Proof/ProjectiveIdealHeight`: commutative-algebra height input
  used by the Tsen/projective common-zero theorem.
- `MatrixSOS/Proof/ComplexFunctionField`: complex function field/Pfister inputs.
- `MatrixSOS/Proof/RationalHahn`: Rational Hahn square roots and positivity witnesses.
- `MatrixSOS/Proof/NoRealRootDescent`: polynomial block cancellation for
  irreducible quadratic factors with no real root.
- `MatrixSOS/Proof/DiagonalReduction`: rational diagonal reduction layers,
  including bilinear-form diagonalization and Smith-kernel compression.
- `MatrixSOS/Proof/FullLineAlgebra`: common denominators, square-extension,
  and rectangular extraction for the full-line proof.
- `MatrixSOS/Proof/FullLine`: exact full-line polynomial matrix factorization
  and the degree extraction used by the bounded theorem.
- `MatrixSOS/Proof/HalfLine.lean` and `MatrixSOS/Proof/Interval`: certificate
  predicates and normalized proof-side constructions for half-lines and finite
  intervals.
- `MatrixSOS/Certificates`: public full-line, half-line, and interval
  certificate APIs, plus scalar and constant special cases.
- `MatrixSOS/Audit.lean`: reproducible public theorem audit.
- `MatrixSOS/Examples.lean`: small public API usage examples.

## References

The main mathematical reference for the full-line matrix SOS theorem is:

- Christoph Hanselka and Rainer Sinn,
  *Positive Semidefinite Univariate Matrix Polynomials*,
  Mathematische Zeitschrift 292 (2019), no. 1-2, 83-101,
  DOI: 10.1007/s00209-018-2137-7.

This repository formalizes the existence of a finite rectangular SOS factor.
It does not formalize the minimal row-count statement or the generic
correspondence with two-square representations of the determinant.

Related work includes:

- Grigoriy Blekherman, Daniel Plaumann, Rainer Sinn, and Cynthia Vinzant,
  *Low-Rank Sum-of-Squares Representations on Varieties of Minimal Degree*,
  International Mathematics Research Notices 2019, no. 1, 33-54.
- Igor Klep and Markus Schweighofer,
  *Pure States, Positive Matrix Polynomials and Sums of Hermitian Squares*,
  Indiana Univ. Math. J. 59 (2010), no. 3, 857-874.
- Victoria Powers and Bruce Reznick,
  *Polynomials That Are Positive on an Interval*,
  Transactions of the American Mathematical Society 352 (2000), no. 10,
  4677-4692.

This formalization also relies on mathlib's Hahn series, lexicographic order,
and binomial-series infrastructure.

For the classical scalar Markov-Lukacs interval and half-line forms, see
Powers-Reznick above.  The matrix statements in this repository are formalized
as matrix-polynomial SOS certificates and are derived from the full-line matrix
SOS theorem.

## Citation and License

Author: **Mocho Go** ([selpoG](https://github.com/selpoG)).

Please cite the software using [CITATION.cff](CITATION.cff), and identify the
release or commit you used so that the cited formalization is reproducible.

Released under the [Apache License 2.0](LICENSE).
