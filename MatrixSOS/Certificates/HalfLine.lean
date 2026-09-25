/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.HalfLine

/-!
# Public certificates for positivity on a half-line
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

theorem nonnegOnNN_affinePullback_one_iff_nonnegOnIci
    {m : ℕ} (a : ℝ) (M : PolyMat m) :
    NonnegOnNN (affinePullbackMat a 1 M) ↔ NonnegOnIci a M := by
  constructor
  · intro h x hx
    have ht : 0 ≤ x - a := by linarith
    have h' := h (x - a) ht
    simpa [one_mul, sub_add_cancel] using h'
  · intro h t ht
    have hx : a ≤ 1 * t + a := by linarith
    simpa using h (1 * t + a) hx

theorem nonnegOnNN_affinePullback_neg_one_iff_nonnegOnIic
    {m : ℕ} (a : ℝ) (M : PolyMat m) :
    NonnegOnNN (affinePullbackMat a (-1) M) ↔ NonnegOnIic a M := by
  constructor
  · intro h x hx
    have ht : 0 ≤ a - x := by linarith
    have h' := h (a - x) ht
    have harg : (-1 : ℝ) * (a - x) + a = x := by ring
    simpa [harg] using h'
  · intro h t ht
    have hx : (-1 : ℝ) * t + a ≤ a := by linarith
    simpa using h ((-1 : ℝ) * t + a) hx

/-- SOS certificate on the Right half-line `[a, ∞)`. -/
def IciSOSCertificate {m : ℕ} (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    IsMatrixSOS S₀ ∧ IsMatrixSOS S₁ ∧
    M = S₀ + (Polynomial.X - Polynomial.C a : Poly) • S₁

/-- Bounded SOS certificate on the Right half-line `[a, ∞)`. -/
private def IciSOSCertificateDegreeBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    BoundedMatrixSOS (evenPartDegreeBound d) S₀ ∧ BoundedMatrixSOS (oddPartDegreeBound d) S₁ ∧
    M = S₀ + (Polynomial.X - Polynomial.C a : Poly) • S₁

/-- Bounded SOS certificate on `[a, ∞)` with both rectangular factors having `m + 1` rows. -/
def IciSOSCertificateBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ (A B : Matrix (Fin (m + 1)) (Fin m) Poly),
    (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
    (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
    M = A.transpose * A + (Polynomial.X - Polynomial.C a : Poly) • (B.transpose * B)

/-- SOS certificate on the Left half-line `(-∞, a]`. -/
def IicSOSCertificate {m : ℕ} (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    IsMatrixSOS S₀ ∧ IsMatrixSOS S₁ ∧
    M = S₀ + (Polynomial.C a - Polynomial.X : Poly) • S₁

/-- Bounded SOS certificate on the Left half-line `(-∞, a]`. -/
private def IicSOSCertificateDegreeBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ S₀ S₁ : PolyMat m,
    BoundedMatrixSOS (evenPartDegreeBound d) S₀ ∧ BoundedMatrixSOS (oddPartDegreeBound d) S₁ ∧
    M = S₀ + (Polynomial.C a - Polynomial.X : Poly) • S₁

/-- Bounded SOS certificate on `(-∞, a]` with both rectangular factors having `m + 1` rows. -/
def IicSOSCertificateBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ (A B : Matrix (Fin (m + 1)) (Fin m) Poly),
    (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
    (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
    M = A.transpose * A + (Polynomial.C a - Polynomial.X : Poly) • (B.transpose * B)

/-- Bounded Gram certificate on the Right half-line `[a, ∞)`. -/
def IciGramCertificateBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ (Y₁ : Matrix (GramIdx (evenPartDegreeBound d) m) (GramIdx (evenPartDegreeBound d) m) ℝ)
    (Y₂ : Matrix (GramIdx (oddPartDegreeBound d) m) (GramIdx (oddPartDegreeBound d) m) ℝ),
    Y₁.PosSemidef ∧ Y₂.PosSemidef ∧
    M = GramTerm (evenPartDegreeBound d) m Y₁ +
      (Polynomial.X - Polynomial.C a : Poly) • GramTerm (oddPartDegreeBound d) m Y₂

/-- Bounded Gram certificate on the Left half-line `(-∞, a]`. -/
def IicGramCertificateBounded {m : ℕ} (d : ℕ) (a : ℝ) (M : PolyMat m) : Prop :=
  ∃ (Y₁ : Matrix (GramIdx (evenPartDegreeBound d) m) (GramIdx (evenPartDegreeBound d) m) ℝ)
    (Y₂ : Matrix (GramIdx (oddPartDegreeBound d) m) (GramIdx (oddPartDegreeBound d) m) ℝ),
    Y₁.PosSemidef ∧ Y₂.PosSemidef ∧
    M = GramTerm (evenPartDegreeBound d) m Y₁ +
      (Polynomial.C a - Polynomial.X : Poly) • GramTerm (oddPartDegreeBound d) m Y₂

lemma affinePullbackMat_halfLine_rhs_one
    {m : ℕ} (a : ℝ) (S₀ S₁ : PolyMat m) :
    affinePullbackMat (-a) 1 (S₀ + (Polynomial.X : Poly) • S₁)
      = affinePullbackMat (-a) 1 S₀
        + (Polynomial.X - Polynomial.C a : Poly) • affinePullbackMat (-a) 1 S₁ := by
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro x
  simp [affinePullbackMat, affinePullbackPoly, Polynomial.eval_comp]
  ring_nf
  simp

lemma affinePullbackMat_halfLine_rhs_neg_one
    {m : ℕ} (a : ℝ) (S₀ S₁ : PolyMat m) :
    affinePullbackMat a (-1) (S₀ + (Polynomial.X : Poly) • S₁)
      = affinePullbackMat a (-1) S₀
        + (Polynomial.C a - Polynomial.X : Poly) • affinePullbackMat a (-1) S₁ := by
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro x
  simp [affinePullbackMat, affinePullbackPoly, Polynomial.eval_comp]
  ring_nf
  simp

theorem iciSOSCertificateBounded_of_normalizedHalfLineSOSCertificateBounded
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
  (hcert :
      NormalizedHalfLineSOSCertificateBounded d (affinePullbackMat a 1 M)) :
    IciSOSCertificateBounded d a M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  refine ⟨affinePullbackMat (-a) 1 A, affinePullbackMat (-a) 1 B, ?_, ?_, ?_⟩
  · intro i j
    exact natDegree_affinePullbackPoly_le (hAdeg i j)
  · intro i j
    exact natDegree_affinePullbackPoly_le (hBdeg i j)
  · have hPull := congrArg (affinePullbackMat (-a) 1) hM
    have hinv : affinePullbackMat (-a) 1 (affinePullbackMat a 1 M) = M := by
      simpa using affinePullbackMat_inverse (a := a) (s := 1) (by norm_num) M
    have hA :
        affinePullbackMat (-a) 1 (A.transpose * A) =
          (affinePullbackMat (-a) 1 A).transpose * affinePullbackMat (-a) 1 A := by
      ext i j
      simp [affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hB :
        affinePullbackMat (-a) 1 (B.transpose * B) =
          (affinePullbackMat (-a) 1 B).transpose * affinePullbackMat (-a) 1 B := by
      ext i j
      simp [affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    rw [hinv] at hPull
    change M =
      affinePullbackMat (-a) 1
        (A.transpose * A + (Polynomial.X : Poly) • (B.transpose * B)) at hPull
    rw [affinePullbackMat_halfLine_rhs_one] at hPull
    simpa [SOSForm, hA, hB] using hPull

theorem iicSOSCertificateBounded_of_normalizedHalfLineSOSCertificateBounded
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
  (hcert :
      NormalizedHalfLineSOSCertificateBounded d (affinePullbackMat a (-1) M)) :
    IicSOSCertificateBounded d a M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  refine ⟨affinePullbackMat a (-1) A, affinePullbackMat a (-1) B, ?_, ?_, ?_⟩
  · intro i j
    exact natDegree_affinePullbackPoly_le (hAdeg i j)
  · intro i j
    exact natDegree_affinePullbackPoly_le (hBdeg i j)
  · have hPull := congrArg (affinePullbackMat a (-1)) hM
    have hinv : affinePullbackMat a (-1) (affinePullbackMat a (-1) M) = M := by
      simpa using affinePullbackMat_inverse (a := a) (s := -1) (by norm_num) M
    have hA :
        affinePullbackMat a (-1) (A.transpose * A) =
          (affinePullbackMat a (-1) A).transpose * affinePullbackMat a (-1) A := by
      ext i j
      simp [affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hB :
        affinePullbackMat a (-1) (B.transpose * B) =
          (affinePullbackMat a (-1) B).transpose * affinePullbackMat a (-1) B := by
      ext i j
      simp [affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    rw [hinv] at hPull
    change M =
      affinePullbackMat a (-1)
        (A.transpose * A + (Polynomial.X : Poly) • (B.transpose * B)) at hPull
    rw [affinePullbackMat_halfLine_rhs_neg_one] at hPull
    simpa [SOSForm, hA, hB] using hPull

theorem nonnegOnIci_of_iciSOSCertificate
    {m : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IciSOSCertificate a M) :
    NonnegOnIci a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  intro x hx
  rw [mapEval_add, mapEval_smul]
  have hweight : 0 ≤ (Polynomial.X - Polynomial.C a : Poly).eval x := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_nonneg.mpr hx
  exact (isMatrixSOS_posSemidef hS₀ x).add
    ((isMatrixSOS_posSemidef hS₁ x).smul hweight)

theorem nonnegOnIic_of_iicSOSCertificate
    {m : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IicSOSCertificate a M) :
    NonnegOnIic a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  intro x hx
  rw [mapEval_add, mapEval_smul]
  have hweight : 0 ≤ (Polynomial.C a - Polynomial.X : Poly).eval x := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_nonneg.mpr hx
  exact (isMatrixSOS_posSemidef hS₀ x).add
    ((isMatrixSOS_posSemidef hS₁ x).smul hweight)

private theorem IciSOSCertificateDegreeBounded.toCertificate
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IciSOSCertificateDegreeBounded d a M) :
    IciSOSCertificate a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, hM⟩
  exact ⟨S₀, S₁, hS₀.isMatrixSOS, hS₁.isMatrixSOS, hM⟩

private theorem IicSOSCertificateDegreeBounded.toCertificate
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IicSOSCertificateDegreeBounded d a M) :
    IicSOSCertificate a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, hM⟩
  exact ⟨S₀, S₁, hS₀.isMatrixSOS, hS₁.isMatrixSOS, hM⟩

private theorem IciSOSCertificateBounded.toDegreeBounded
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IciSOSCertificateBounded d a M) :
    IciSOSCertificateDegreeBounded d a M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  exact ⟨A.transpose * A, B.transpose * B,
    ⟨m + 1, A, hAdeg, rfl⟩, ⟨m + 1, B, hBdeg, rfl⟩, hM⟩

private theorem IicSOSCertificateBounded.toDegreeBounded
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IicSOSCertificateBounded d a M) :
    IicSOSCertificateDegreeBounded d a M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hM⟩
  exact ⟨A.transpose * A, B.transpose * B,
    ⟨m + 1, A, hAdeg, rfl⟩, ⟨m + 1, B, hBdeg, rfl⟩, hM⟩

private theorem iciSOSCertificateBounded_to_gram
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IciSOSCertificateDegreeBounded d a M) :
    IciGramCertificateBounded d a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  rcases boundedMatrixSOS_to_gramTerm hS₀ with ⟨Y₁, hY₁, hS₀Y⟩
  rcases boundedMatrixSOS_to_gramTerm hS₁ with ⟨Y₂, hY₂, hS₁Y⟩
  exact ⟨Y₁, Y₂, hY₁, hY₂, by simp [hS₀Y, hS₁Y]⟩

private theorem iicSOSCertificateBounded_to_gram
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IicSOSCertificateDegreeBounded d a M) :
    IicGramCertificateBounded d a M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  rcases boundedMatrixSOS_to_gramTerm hS₀ with ⟨Y₁, hY₁, hS₀Y⟩
  rcases boundedMatrixSOS_to_gramTerm hS₁ with ⟨Y₂, hY₂, hS₁Y⟩
  exact ⟨Y₁, Y₂, hY₁, hY₂, by simp [hS₀Y, hS₁Y]⟩

theorem iciSOSCertificate_of_gram
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IciGramCertificateBounded d a M) :
    IciSOSCertificate a M := by
  rcases hcert with ⟨Y₁, Y₂, hY₁, hY₂, hM⟩
  exact ⟨GramTerm (evenPartDegreeBound d) m Y₁, GramTerm (oddPartDegreeBound d) m Y₂,
    isMatrixSOS_gramTerm_of_posSemidef hY₁,
    isMatrixSOS_gramTerm_of_posSemidef hY₂, hM⟩

theorem iicSOSCertificate_of_gram
    {m d : ℕ} {a : ℝ} {M : PolyMat m}
    (hcert : IicGramCertificateBounded d a M) :
    IicSOSCertificate a M := by
  rcases hcert with ⟨Y₁, Y₂, hY₁, hY₂, hM⟩
  exact ⟨GramTerm (evenPartDegreeBound d) m Y₁, GramTerm (oddPartDegreeBound d) m Y₂,
    isMatrixSOS_gramTerm_of_posSemidef hY₁,
    isMatrixSOS_gramTerm_of_posSemidef hY₂, hM⟩

/--
Bounded Right half-line SOS certificate with both rectangular factors having
`m + 1` rows.
-/
private theorem posSemidefOn_Ici_exists_sos_bounded
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm)
    (hM : NonnegOnIci a M) :
    IciSOSCertificateBounded d a M := by
  have hsymm' : (affinePullbackMat a 1 M).IsSymm :=
    affinePullbackMat_isSymm hsymm
  have hdeg' : ∀ i j, natDegree (affinePullbackMat a 1 M i j) ≤ d :=
    natDegree_affinePullbackMat_le hdeg
  have hNN : NonnegOnNN (affinePullbackMat a 1 M) :=
    (nonnegOnNN_affinePullback_one_iff_nonnegOnIci a M).2 hM
  exact iciSOSCertificateBounded_of_normalizedHalfLineSOSCertificateBounded
    (halfLine_sosCertificate_bounded
      (affinePullbackMat a 1 M) hdeg' hsymm' hNN)

/--
Bounded Right half-line SOS certificate with both rectangular factors having
`m + 1` rows, stated as an iff.
-/
theorem posSemidefOn_Ici_iff_sos
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciSOSCertificateBounded d a M := by
  constructor
  · exact posSemidefOn_Ici_exists_sos_bounded a M hdeg hsymm
  · intro hcert
    exact nonnegOnIci_of_iciSOSCertificate hcert.toDegreeBounded.toCertificate

/--
Bounded Right half-line Gram certificate.

The Gram matrices certify `M` itself in the endpoint form
`GramTerm + (X - a) • GramTerm`.
-/
theorem posSemidefOn_Ici_iff_gram
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciGramCertificateBounded d a M := by
  constructor
  · intro hM
    exact iciSOSCertificateBounded_to_gram
      ((posSemidefOn_Ici_iff_sos a M hdeg hsymm).1 hM).toDegreeBounded
  · intro hcert
    exact nonnegOnIci_of_iciSOSCertificate (iciSOSCertificate_of_gram hcert)

/--
Bounded Left half-line SOS certificate with both rectangular factors having
`m + 1` rows.
-/
private theorem posSemidefOn_Iic_exists_sos_bounded
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm)
    (hM : NonnegOnIic a M) :
    IicSOSCertificateBounded d a M := by
  have hsymm' : (affinePullbackMat a (-1) M).IsSymm :=
    affinePullbackMat_isSymm hsymm
  have hdeg' : ∀ i j, natDegree (affinePullbackMat a (-1) M i j) ≤ d :=
    natDegree_affinePullbackMat_le hdeg
  have hNN : NonnegOnNN (affinePullbackMat a (-1) M) :=
    (nonnegOnNN_affinePullback_neg_one_iff_nonnegOnIic a M).2 hM
  exact iicSOSCertificateBounded_of_normalizedHalfLineSOSCertificateBounded
    (halfLine_sosCertificate_bounded
      (affinePullbackMat a (-1) M) hdeg' hsymm' hNN)

/--
Bounded Left half-line SOS certificate with both rectangular factors having
`m + 1` rows, stated as an iff.
-/
theorem posSemidefOn_Iic_iff_sos
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIic a M ↔ IicSOSCertificateBounded d a M := by
  constructor
  · exact posSemidefOn_Iic_exists_sos_bounded a M hdeg hsymm
  · intro hcert
    exact nonnegOnIic_of_iicSOSCertificate hcert.toDegreeBounded.toCertificate

/--
Bounded Left half-line Gram certificate.

The Gram matrices certify `M` itself in the endpoint form
`GramTerm + (a - X) • GramTerm`.
-/
theorem posSemidefOn_Iic_iff_gram
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIic a M ↔ IicGramCertificateBounded d a M := by
  constructor
  · intro hM
    exact iicSOSCertificateBounded_to_gram
      ((posSemidefOn_Iic_iff_sos a M hdeg hsymm).1 hM).toDegreeBounded
  · intro hcert
    exact nonnegOnIic_of_iicSOSCertificate (iicSOSCertificate_of_gram hcert)

namespace Certificates

namespace HalfLine

/-- Public bounded Right half-line SOS certificate with fixed row count. -/
theorem posSemidefOn_Ici_iff_sos
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciSOSCertificateBounded d a M :=
  _root_.MatrixSOS.posSemidefOn_Ici_iff_sos a M hdeg hsymm

/-- Public bounded Left half-line SOS certificate with fixed row count. -/
theorem posSemidefOn_Iic_iff_sos
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIic a M ↔ IicSOSCertificateBounded d a M :=
  _root_.MatrixSOS.posSemidefOn_Iic_iff_sos a M hdeg hsymm

/-- Public bounded Right half-line Gram certificate. -/
theorem posSemidefOn_Ici_iff_gram
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIci a M ↔ IciGramCertificateBounded d a M :=
  _root_.MatrixSOS.posSemidefOn_Ici_iff_gram a M hdeg hsymm

/-- Public bounded Left half-line Gram certificate. -/
theorem posSemidefOn_Iic_iff_gram
    {m d : ℕ} (a : ℝ) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm) :
    NonnegOnIic a M ↔ IicGramCertificateBounded d a M :=
  _root_.MatrixSOS.posSemidefOn_Iic_iff_gram a M hdeg hsymm

end HalfLine

end Certificates

end MatrixSOS
