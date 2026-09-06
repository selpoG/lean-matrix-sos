/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.PolyMatrix

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

/-- The Markov-Lukacs interval weight `(X - a) * (b - X)`. -/
def intervalWeight (a b : ℝ) : Poly :=
  (Polynomial.X - Polynomial.C a) * (Polynomial.C b - Polynomial.X)

/--
Even-degree Markov-Lukacs-type interval certificate:
`M = S₀ + (X - a) * (b - X) • S₁` with `S₀` and `S₁` SOS.
-/
def IccLukacsCertificate {m : ℕ} (a b : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    IsMatrixSOS S₀ ∧ IsMatrixSOS S₁ ∧
    M = S₀ + intervalWeight a b • S₁

/--
Odd-degree Markov-Lukacs-type interval certificate:
`M = (X - a) • S₀ + (b - X) • S₁` with `S₀` and `S₁` SOS.
-/
def IccLukacsCertificateOdd {m : ℕ} (a b : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    IsMatrixSOS S₀ ∧ IsMatrixSOS S₁ ∧
    M = (Polynomial.X - Polynomial.C a) • S₀ + (Polynomial.C b - Polynomial.X) • S₁

/--
Degree bound for the second SOS factor in the even finite-interval
Markov-Lukacs certificate.

Mathematically this is the `d - 1` bound.  For `d = 0`, Lean records the bound
as `0`; the weighted second term is then forced to vanish by the certificate
identity in the degree-zero case.
-/
def intervalEvenSecondDegreeBound (d : ℕ) : ℕ := d - 1

/--
Tightly bounded even-degree Markov-Lukacs interval certificate:
`S₀` has SOS factors of degree at most `d`, and `S₁` has SOS factors of
degree at most `intervalEvenSecondDegreeBound d`.
-/
def IccLukacsCertificateDegreeBoundedEven {m : ℕ} (d : ℕ) (a b : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    BoundedMatrixSOS d S₀ ∧ BoundedMatrixSOS (intervalEvenSecondDegreeBound d) S₁ ∧
    M = S₀ + intervalWeight a b • S₁

/--
Tightly bounded even-degree interval certificate with both rectangular factors
having exactly `m + 1` rows.
-/
def IccLukacsCertificateBoundedEven {m : ℕ} (d : ℕ) (a b : ℝ)
    (M : PolyMat m) : Prop :=
  ∃ (A B : Matrix (Fin (m + 1)) (Fin m) Poly),
    (∀ i j, natDegree (A i j) ≤ d) ∧
    (∀ i j, natDegree (B i j) ≤ intervalEvenSecondDegreeBound d) ∧
    M = A.transpose * A + intervalWeight a b • (B.transpose * B)

/--
Tightly bounded odd-degree Markov-Lukacs interval certificate:
both SOS factors have degree at most `d`.
-/
def IccLukacsCertificateDegreeBoundedOdd {m : ℕ} (d : ℕ) (a b : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    BoundedMatrixSOS d S₀ ∧ BoundedMatrixSOS d S₁ ∧
    M = (Polynomial.X - Polynomial.C a) • S₀ + (Polynomial.C b - Polynomial.X) • S₁

/--
Tightly bounded odd-degree interval certificate with both rectangular factors
having exactly `m + 1` rows.
-/
def IccLukacsCertificateBoundedOdd {m : ℕ} (d : ℕ) (a b : ℝ)
    (M : PolyMat m) : Prop :=
  ∃ (A B : Matrix (Fin (m + 1)) (Fin m) Poly),
    (∀ i j, natDegree (A i j) ≤ d) ∧
    (∀ i j, natDegree (B i j) ≤ d) ∧
    M = (Polynomial.X - Polynomial.C a) • (A.transpose * A)
      + (Polynomial.C b - Polynomial.X) • (B.transpose * B)

/--
Bounded even-degree Markov-Lukacs Gram certificate:
`M = Q_dᵀ Y₀ Q_d + (X - a) * (b - X) • Q_{d-1}ᵀ Y₁ Q_{d-1}`.
-/
def IccLukacsGramCertificateBoundedEven {m : ℕ} (d : ℕ) (a b : ℝ)
    (M : PolyMat m) : Prop :=
  ∃ (Y₀ : Matrix (GramIdx d m) (GramIdx d m) ℝ)
    (Y₁ : Matrix (GramIdx (intervalEvenSecondDegreeBound d) m)
      (GramIdx (intervalEvenSecondDegreeBound d) m) ℝ),
    Y₀.PosSemidef ∧ Y₁.PosSemidef ∧
    M = GramTerm d m Y₀
      + intervalWeight a b • GramTerm (intervalEvenSecondDegreeBound d) m Y₁

/--
Bounded odd-degree Markov-Lukacs Gram certificate:
`M = (X - a) • Q_dᵀ Y₀ Q_d + (b - X) • Q_dᵀ Y₁ Q_d`.
-/
def IccLukacsGramCertificateBoundedOdd {m : ℕ} (d : ℕ) (a b : ℝ)
    (M : PolyMat m) : Prop :=
  ∃ (Y₀ : Matrix (GramIdx d m) (GramIdx d m) ℝ)
    (Y₁ : Matrix (GramIdx d m) (GramIdx d m) ℝ),
    Y₀.PosSemidef ∧ Y₁.PosSemidef ∧
    M = (Polynomial.X - Polynomial.C a) • GramTerm d m Y₀
      + (Polynomial.C b - Polynomial.X) • GramTerm d m Y₁

theorem IccLukacsCertificateDegreeBoundedEven.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateDegreeBoundedEven d a b M) :
    IccLukacsCertificate a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, hM⟩
  exact ⟨S₀, S₁, hS₀.isMatrixSOS, hS₁.isMatrixSOS, hM⟩

theorem IccLukacsCertificateBoundedEven.toDegreeBounded
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedEven d a b M) :
    IccLukacsCertificateDegreeBoundedEven d a b M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  exact ⟨A.transpose * A, B.transpose * B, ⟨m + 1, A, hAdeg, rfl⟩,
    ⟨m + 1, B, hBdeg, rfl⟩, hM⟩

theorem IccLukacsCertificateDegreeBoundedOdd.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateDegreeBoundedOdd d a b M) :
    IccLukacsCertificateOdd a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, hM⟩
  exact ⟨S₀, S₁, hS₀.isMatrixSOS, hS₁.isMatrixSOS, hM⟩

theorem IccLukacsCertificateBoundedOdd.toDegreeBounded
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedOdd d a b M) :
    IccLukacsCertificateDegreeBoundedOdd d a b M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  exact ⟨A.transpose * A, B.transpose * B, ⟨m + 1, A, hAdeg, rfl⟩,
    ⟨m + 1, B, hBdeg, rfl⟩, hM⟩

theorem IccLukacsCertificateDegreeBoundedEven.toGram
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateDegreeBoundedEven d a b M) :
    IccLukacsGramCertificateBoundedEven d a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  rcases boundedMatrixSOS_to_gramTerm hS₀ with ⟨Y₀, hY₀, hS₀Y⟩
  rcases boundedMatrixSOS_to_gramTerm hS₁ with ⟨Y₁, hY₁, hS₁Y⟩
  exact ⟨Y₀, Y₁, hY₀, hY₁, by simp [hS₀Y, hS₁Y]⟩

theorem IccLukacsCertificateDegreeBoundedOdd.toGram
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateDegreeBoundedOdd d a b M) :
    IccLukacsGramCertificateBoundedOdd d a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  rcases boundedMatrixSOS_to_gramTerm hS₀ with ⟨Y₀, hY₀, hS₀Y⟩
  rcases boundedMatrixSOS_to_gramTerm hS₁ with ⟨Y₁, hY₁, hS₁Y⟩
  exact ⟨Y₀, Y₁, hY₀, hY₁, by simp [hS₀Y, hS₁Y]⟩

theorem IccLukacsCertificateBoundedEven.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedEven d a b M) :
    IccLukacsCertificate a b M :=
  hcert.toDegreeBounded.toCertificate

theorem IccLukacsCertificateBoundedOdd.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedOdd d a b M) :
    IccLukacsCertificateOdd a b M :=
  hcert.toDegreeBounded.toCertificate

theorem IccLukacsCertificateBoundedEven.toGram
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedEven d a b M) :
    IccLukacsGramCertificateBoundedEven d a b M :=
  hcert.toDegreeBounded.toGram

theorem IccLukacsCertificateBoundedOdd.toGram
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateBoundedOdd d a b M) :
    IccLukacsGramCertificateBoundedOdd d a b M :=
  hcert.toDegreeBounded.toGram

theorem IccLukacsGramCertificateBoundedEven.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsGramCertificateBoundedEven d a b M) :
    IccLukacsCertificate a b M := by
  rcases hcert with ⟨Y₀, Y₁, hY₀, hY₁, hM⟩
  exact ⟨GramTerm d m Y₀, GramTerm (intervalEvenSecondDegreeBound d) m Y₁,
    isMatrixSOS_gramTerm_of_posSemidef hY₀,
    isMatrixSOS_gramTerm_of_posSemidef hY₁, hM⟩

theorem IccLukacsGramCertificateBoundedOdd.toCertificate
    {m d : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsGramCertificateBoundedOdd d a b M) :
    IccLukacsCertificateOdd a b M := by
  rcases hcert with ⟨Y₀, Y₁, hY₀, hY₁, hM⟩
  exact ⟨GramTerm d m Y₀, GramTerm d m Y₁,
    isMatrixSOS_gramTerm_of_posSemidef hY₀,
    isMatrixSOS_gramTerm_of_posSemidef hY₁, hM⟩

end MatrixSOS
