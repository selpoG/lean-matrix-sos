/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.Interval.Normalized
import MatrixSOS.Proof.Interval.Certificates
import MatrixSOS.Certificates.FullLine

/-!
# Public certificates for positivity on a closed interval
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

/--
Affine reindexing between `[0, 1]` and `[a, b]`.

The statement is formulated for `a ≤ b`; the degenerate case is handled
directly.
-/
theorem posSemidefOn_Icc_affinePullback_iff
    {m : ℕ} {a b : ℝ} (hab : a ≤ b) (M : PolyMat m) :
    NonnegOnIcc 0 1 (affinePullbackMat a (b - a) M) ↔
    NonnegOnIcc a b M := by
  constructor
  · intro h x hax hxb
    by_cases hlt : a < b
    · let t : ℝ := (x - a) / (b - a)
      have hden : 0 < b - a := sub_pos.mpr hlt
      have ht0 : 0 ≤ t := by
        exact div_nonneg (sub_nonneg.mpr hax) hden.le
      have ht1 : t ≤ 1 := by
        rw [div_le_one hden]
        linarith
      have harg : (b - a) * t + a = x := by
        dsimp [t]
        field_simp [hden.ne']
        ring
      simpa [harg] using h t ht0 ht1
    · have hba : b = a := le_antisymm (le_of_not_gt hlt) hab
      have hx : x = a := le_antisymm (by simpa [hba] using hxb) hax
      simpa [hba, hx] using h 0 (by norm_num) (by norm_num)
  · intro h t ht0 ht1
    have hleft : a ≤ (b - a) * t + a := by
      nlinarith [sub_nonneg.mpr hab, ht0]
    have hright : (b - a) * t + a ≤ b := by
      nlinarith [sub_nonneg.mpr hab, ht1]
    simpa using h ((b - a) * t + a) hleft hright

lemma affinePullbackPoly_unitIntervalWeight
    {a b : ℝ} (hs : b - a ≠ 0) :
    affinePullbackPoly (-a / (b - a)) (1 / (b - a)) (intervalWeight 0 1) =
      Polynomial.C ((1 / (b - a)) ^ 2) * intervalWeight a b := by
  apply Polynomial.funext
  intro x
  simp [affinePullbackPoly, intervalWeight]
  field_simp [hs]
  ring

lemma affinePullbackPoly_unitIntervalLeftWeight
    {a b : ℝ} (hs : b - a ≠ 0) :
    affinePullbackPoly (-a / (b - a)) (1 / (b - a))
        (Polynomial.X - Polynomial.C 0 : Poly) =
      Polynomial.C (1 / (b - a)) * (Polynomial.X - Polynomial.C a) := by
  apply Polynomial.funext
  intro x
  simp [affinePullbackPoly]
  field_simp [hs]
  ring

lemma affinePullbackPoly_unitIntervalRightWeight
    {a b : ℝ} (hs : b - a ≠ 0) :
    affinePullbackPoly (-a / (b - a)) (1 / (b - a))
        (Polynomial.C 1 - Polynomial.X : Poly) =
      Polynomial.C (1 / (b - a)) * (Polynomial.C b - Polynomial.X) := by
  apply Polynomial.funext
  intro x
  simp [affinePullbackPoly]
  field_simp [hs]
  ring

lemma transpose_mul_const_smul
    {m ℓ : ℕ} (c : ℝ) (A : Matrix (Fin ℓ) (Fin m) Poly) :
    (Polynomial.C c • A).transpose * (Polynomial.C c • A) =
      (Polynomial.C (c ^ 2) : Poly) • (A.transpose * A) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, pow_two, mul_assoc, mul_left_comm, mul_comm]

lemma iccLukacsSOSBoundedEven_of_unit_affine
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hcert : IccLukacsCertificateBoundedEven d 0 1
      (affinePullbackMat a (b - a) M)) :
    IccLukacsCertificateBoundedEven d a b M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hEq⟩
  let s : ℝ := b - a
  have hs : s ≠ 0 := by
    dsimp [s]
    exact sub_ne_zero.mpr hab.ne'
  let A' : Matrix (Fin (m + 1)) (Fin m) Poly := affinePullbackMat (-a / s) (1 / s) A
  let Bbase : Matrix (Fin (m + 1)) (Fin m) Poly := affinePullbackMat (-a / s) (1 / s) B
  let c : ℝ := 1 / s
  let B' : Matrix (Fin (m + 1)) (Fin m) Poly := Polynomial.C c • Bbase
  refine ⟨A', B', ?_, ?_, ?_⟩
  · intro i j
    exact natDegree_affinePullbackPoly_le (hAdeg i j)
  · intro i j
    exact (Polynomial.natDegree_C_mul_le c (Bbase i j)).trans
      (natDegree_affinePullbackPoly_le (hBdeg i j))
  · have hPull := congrArg (affinePullbackMat (-a / s) (1 / s)) hEq
    change
      affinePullbackMat (-a / s) (1 / s) (affinePullbackMat a s M) =
        affinePullbackMat (-a / s) (1 / s)
          (A.transpose * A + intervalWeight 0 1 • (B.transpose * B)) at hPull
    rw [affinePullbackMat_inverse hs M] at hPull
    have hA :
        affinePullbackMat (-a / s) (1 / s) (A.transpose * A) =
          A'.transpose * A' := by
      ext i j
      simp [A', affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hB :
        affinePullbackMat (-a / s) (1 / s) (B.transpose * B) =
          Bbase.transpose * Bbase := by
      ext i j
      simp [Bbase, affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hScale :
        B'.transpose * B' =
          (Polynomial.C ((1 / s) ^ 2) : Poly) • (Bbase.transpose * Bbase) := by
      simpa [B', c] using transpose_mul_const_smul (1 / s) Bbase
    have hRhs :
        affinePullbackMat (-a / s) (1 / s)
          (A.transpose * A + intervalWeight 0 1 • (B.transpose * B)) =
          A'.transpose * A' + intervalWeight a b •
            ((Polynomial.C ((1 / s) ^ 2) : Poly) • (Bbase.transpose * Bbase)) := by
      apply Matrix.ext
      intro i j
      apply Polynomial.funext
      intro x
      simp only [A', Bbase, affinePullbackMat, Matrix.add_apply, Matrix.smul_apply,
        affinePullbackPoly, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul]
      simp only [smul_eq_mul, Polynomial.eval_mul]
      have hw := congrArg (fun p : Poly => p.eval x)
        (affinePullbackPoly_unitIntervalWeight (a := a) (b := b) (by simpa [s] using hs))
      simp only [affinePullbackPoly, Polynomial.eval_mul, Polynomial.eval_C] at hw
      have hw' :
          eval (eval x (Polynomial.C (1 / s)) * eval x Polynomial.X +
              eval x (Polynomial.C (-a / s))) (intervalWeight 0 1) =
            (1 / s) ^ 2 * eval x (intervalWeight a b) := by
        simpa [s, Polynomial.eval_comp] using hw
      have hAeval := congrArg (fun p : Poly => p.eval x) (congrArg (fun N => N i j) hA)
      have hBeval := congrArg (fun p : Poly => p.eval x) (congrArg (fun N => N i j) hB)
      simp only [A', Bbase, affinePullbackMat, affinePullbackPoly, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hAeval hBeval
      simp only [Polynomial.eval_C, Polynomial.eval_X]
      rw [hAeval, hBeval]
      simp only [Polynomial.eval_C, Polynomial.eval_X] at hw'
      rw [hw']
      ring
    rw [hRhs] at hPull
    rw [hScale]
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hPull

lemma iccLukacsSOSBoundedOdd_of_unit_affine
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hcert : IccLukacsCertificateBoundedOdd d 0 1
      (affinePullbackMat a (b - a) M)) :
    IccLukacsCertificateBoundedOdd d a b M := by
  rcases hcert with ⟨A, B, hAdeg, hBdeg, hEq⟩
  let s : ℝ := b - a
  have hs : s ≠ 0 := by
    dsimp [s]
    exact sub_ne_zero.mpr hab.ne'
  have hspos : 0 < s := by
    dsimp [s]
    exact sub_pos.mpr hab
  let c : ℝ := 1 / s
  let r : ℝ := Real.sqrt c
  have hc_nonneg : 0 ≤ c := by
    simpa [c, one_div] using inv_nonneg.mpr hspos.le
  have hr2 : r ^ 2 = c := by
    dsimp [r]
    exact Real.sq_sqrt hc_nonneg
  let Abase : Matrix (Fin (m + 1)) (Fin m) Poly := affinePullbackMat (-a / s) (1 / s) A
  let Bbase : Matrix (Fin (m + 1)) (Fin m) Poly := affinePullbackMat (-a / s) (1 / s) B
  let A' : Matrix (Fin (m + 1)) (Fin m) Poly := Polynomial.C r • Abase
  let B' : Matrix (Fin (m + 1)) (Fin m) Poly := Polynomial.C r • Bbase
  refine ⟨A', B', ?_, ?_, ?_⟩
  · intro i j
    exact (Polynomial.natDegree_C_mul_le r (Abase i j)).trans
      (natDegree_affinePullbackPoly_le (hAdeg i j))
  · intro i j
    exact (Polynomial.natDegree_C_mul_le r (Bbase i j)).trans
      (natDegree_affinePullbackPoly_le (hBdeg i j))
  · have hPull := congrArg (affinePullbackMat (-a / s) (1 / s)) hEq
    change
      affinePullbackMat (-a / s) (1 / s) (affinePullbackMat a s M) =
        affinePullbackMat (-a / s) (1 / s)
          ((Polynomial.X - Polynomial.C 0 : Poly) • (A.transpose * A) +
            (Polynomial.C 1 - Polynomial.X : Poly) • (B.transpose * B)) at hPull
    rw [affinePullbackMat_inverse hs M] at hPull
    have hA :
        affinePullbackMat (-a / s) (1 / s) (A.transpose * A) =
          Abase.transpose * Abase := by
      ext i j
      simp [Abase, affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hB :
        affinePullbackMat (-a / s) (1 / s) (B.transpose * B) =
          Bbase.transpose * Bbase := by
      ext i j
      simp [Bbase, affinePullbackMat, affinePullbackPoly, Matrix.mul_apply]
    have hScaleA :
        A'.transpose * A' =
          (Polynomial.C c : Poly) • (Abase.transpose * Abase) := by
      calc
        A'.transpose * A' =
            (Polynomial.C r • Abase).transpose * (Polynomial.C r • Abase) := by
          rfl
        _ = (Polynomial.C (r ^ 2) : Poly) • (Abase.transpose * Abase) :=
          transpose_mul_const_smul r Abase
        _ = (Polynomial.C c : Poly) • (Abase.transpose * Abase) := by
          rw [hr2]
    have hScaleB :
        B'.transpose * B' =
          (Polynomial.C c : Poly) • (Bbase.transpose * Bbase) := by
      calc
        B'.transpose * B' =
            (Polynomial.C r • Bbase).transpose * (Polynomial.C r • Bbase) := by
          rfl
        _ = (Polynomial.C (r ^ 2) : Poly) • (Bbase.transpose * Bbase) :=
          transpose_mul_const_smul r Bbase
        _ = (Polynomial.C c : Poly) • (Bbase.transpose * Bbase) := by
          rw [hr2]
    have hRhs :
        affinePullbackMat (-a / s) (1 / s)
          ((Polynomial.X - Polynomial.C 0 : Poly) • (A.transpose * A) +
            (Polynomial.C 1 - Polynomial.X : Poly) • (B.transpose * B)) =
          (Polynomial.X - Polynomial.C a : Poly) •
              ((Polynomial.C c : Poly) • (Abase.transpose * Abase)) +
            (Polynomial.C b - Polynomial.X : Poly) •
              ((Polynomial.C c : Poly) • (Bbase.transpose * Bbase)) := by
      apply Matrix.ext
      intro i j
      apply Polynomial.funext
      intro x
      simp only [Abase, Bbase, affinePullbackMat, Matrix.add_apply, Matrix.smul_apply,
        affinePullbackPoly, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_mul, smul_eq_mul]
      have hleft := congrArg (fun p : Poly => p.eval x)
        (affinePullbackPoly_unitIntervalLeftWeight (a := a) (b := b) (by simpa [s] using hs))
      have hright := congrArg (fun p : Poly => p.eval x)
        (affinePullbackPoly_unitIntervalRightWeight (a := a) (b := b) (by simpa [s] using hs))
      simp only [affinePullbackPoly, Polynomial.eval_mul, Polynomial.eval_C] at hleft hright
      have hAeval := congrArg (fun p : Poly => p.eval x) (congrArg (fun N => N i j) hA)
      have hBeval := congrArg (fun p : Poly => p.eval x) (congrArg (fun N => N i j) hB)
      simp only [Abase, Bbase, affinePullbackMat, affinePullbackPoly, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hAeval hBeval
      simp only [Polynomial.eval_C, Polynomial.eval_X]
      rw [hAeval, hBeval]
      rw [show eval (1 / s * x + -a / s) (Polynomial.X - Polynomial.C 0 : Poly) =
            c * eval x (Polynomial.X - Polynomial.C a : Poly) by
              simpa [s, c, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_C, Polynomial.eval_X] using hleft]
      rw [show eval (1 / s * x + -a / s) (Polynomial.C 1 - Polynomial.X : Poly) =
            c * eval x (Polynomial.C b - Polynomial.X : Poly) by
              simpa [s, c, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_C, Polynomial.eval_X] using hright]
      simp only [c]
      ring
    rw [hRhs] at hPull
    rw [hScaleA, hScaleB]
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hPull

/--
Finite-interval even-shape theorem with bounded input degree and fixed row count.

The SOS factors in both summands are represented with `m + 1` rows.
-/
theorem posSemidefOn_Icc_iff_lukacsSOS_even
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsCertificateBoundedEven d a b M := by
  constructor
  · intro hM
    have hN : NonnegOnIcc 0 1 (affinePullbackMat a (b - a) M) :=
      (posSemidefOn_Icc_affinePullback_iff hab.le M).2 hM
    have hNdeg : ∀ i j, natDegree (affinePullbackMat a (b - a) M i j) ≤ 2 * d :=
      natDegree_affinePullbackMat_le hdeg
    have hsymmN : (affinePullbackMat a (b - a) M).IsSymm :=
      affinePullbackMat_isSymm hsymm
    by_cases hd : 0 < d
    · exact iccLukacsSOSBoundedEven_of_unit_affine hab M
        (unitInterval_lukacsSOS_bounded_even hd
          (affinePullbackMat a (b - a) M) hNdeg hsymmN hN)
    · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      subst d
      have hdeg0 : ∀ i j, natDegree (M i j) ≤ 0 := by
        simpa using hdeg
      have hconst : M = constPolyMat (mapEval 0 M) :=
        eq_constPolyMat_of_natDegree_le_zero M hdeg0
      have hMall : ∀ x : ℝ, (mapEval x M).PosSemidef := by
        intro x
        have ha : (mapEval a M).PosSemidef := hM a (le_refl a) hab.le
        rw [hconst, mapEval_constPolyMat] at ha
        rw [hconst, mapEval_constPolyMat]
        exact ha
      rcases (fullLine_posSemidef_iff_sos (d := 0)
          M (by simpa using hdeg0) hsymm).1 hMall with
        ⟨R, hRdeg, hR⟩
      refine ⟨R, 0, hRdeg, ?_, ?_⟩
      · intro i j
        simp
      · simp [hR]
  · intro hcert
    exact nonnegOnIcc_of_lukacsSOS hcert.toCertificate

/--
Finite-interval even-shape theorem in bounded Gram form.

This is the Gram-matrix repackaging of
`posSemidefOn_Icc_iff_lukacsSOS_even`.
-/
theorem posSemidefOn_Icc_iff_lukacsGram_even
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsGramCertificateBoundedEven d a b M := by
  constructor
  · intro hM
    exact ((posSemidefOn_Icc_iff_lukacsSOS_even
      hab M hdeg hsymm).1 hM).toGram
  · intro hcert
    exact nonnegOnIcc_of_lukacsSOS hcert.toCertificate

/--
Finite-interval odd-shape theorem with bounded input degree and fixed row count.

The SOS factors in both summands are represented with `m + 1` rows.
-/
theorem posSemidefOn_Icc_iff_lukacsSOS_odd
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsCertificateBoundedOdd d a b M := by
  constructor
  · intro hM
    have hN : NonnegOnIcc 0 1 (affinePullbackMat a (b - a) M) :=
      (posSemidefOn_Icc_affinePullback_iff hab.le M).2 hM
    have hNdeg : ∀ i j, natDegree (affinePullbackMat a (b - a) M i j) ≤ 2 * d + 1 :=
      natDegree_affinePullbackMat_le hdeg
    have hsymmN : (affinePullbackMat a (b - a) M).IsSymm :=
      affinePullbackMat_isSymm hsymm
    exact iccLukacsSOSBoundedOdd_of_unit_affine hab M
      (unitInterval_lukacsSOS_bounded_odd
        (affinePullbackMat a (b - a) M) hNdeg hsymmN hN)
  · intro hcert
    exact nonnegOnIcc_of_lukacsOddSOS hcert.toCertificate

/--
Finite-interval odd-shape theorem in bounded Gram form.

This is the Gram-matrix repackaging of
`posSemidefOn_Icc_iff_lukacsSOS_odd`.
-/
theorem posSemidefOn_Icc_iff_lukacsGram_odd
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsGramCertificateBoundedOdd d a b M := by
  constructor
  · intro hM
    exact ((posSemidefOn_Icc_iff_lukacsSOS_odd
      hab M hdeg hsymm).1 hM).toGram
  · intro hcert
    exact nonnegOnIcc_of_lukacsOddSOS hcert.toCertificate

namespace Certificates

namespace Interval

/-- Public affine reindexing theorem for finite intervals. -/
theorem posSemidefOn_Icc_affinePullback_iff
    {m : ℕ} {a b : ℝ} (hab : a ≤ b) (M : PolyMat m) :
    NonnegOnIcc 0 1 (affinePullbackMat a (b - a) M) ↔
    NonnegOnIcc a b M :=
  _root_.MatrixSOS.posSemidefOn_Icc_affinePullback_iff hab M

/-- Public finite-interval even-shape theorem with bounded degree and fixed row count. -/
theorem posSemidefOn_Icc_iff_lukacsSOS_even
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsCertificateBoundedEven d a b M :=
  _root_.MatrixSOS.posSemidefOn_Icc_iff_lukacsSOS_even
    hab M hdeg hsymm

/-- Public finite-interval even-shape theorem in bounded Gram form. -/
theorem posSemidefOn_Icc_iff_lukacsGram_even
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsGramCertificateBoundedEven d a b M :=
  _root_.MatrixSOS.posSemidefOn_Icc_iff_lukacsGram_even hab M hdeg hsymm

/-- Public finite-interval odd-shape theorem with bounded degree and fixed row count. -/
theorem posSemidefOn_Icc_iff_lukacsSOS_odd
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsCertificateBoundedOdd d a b M :=
  _root_.MatrixSOS.posSemidefOn_Icc_iff_lukacsSOS_odd
    hab M hdeg hsymm

/-- Public finite-interval odd-shape theorem in bounded Gram form. -/
theorem posSemidefOn_Icc_iff_lukacsGram_odd
    {m d : ℕ} {a b : ℝ} (hab : a < b) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1) (hsymm : M.IsSymm) :
    NonnegOnIcc a b M ↔ IccLukacsGramCertificateBoundedOdd d a b M :=
  _root_.MatrixSOS.posSemidefOn_Icc_iff_lukacsGram_odd hab M hdeg hsymm

end Interval

end Certificates

end MatrixSOS
