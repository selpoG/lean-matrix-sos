/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.PairBlocks
import MatrixSOS.Proof.NoRealRootDescent.Parity.BlockFactorization

/-!
# Vanishing at complex roots in polynomial matrix descent
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS
theorem mapEvalComplex_eq_zero_of_entrywiseDvdBy
    {ι κ : Type*}
    {p : Poly}
    {z : ℂ}
    {A : Matrix ι κ Poly}
    (hpz : eval₂ (algebraMap ℝ ℂ) z p = 0)
    (hA : EntrywiseDvdBy p A) :
    mapEvalComplex z A = 0 := by
  ext i j
  rcases hA i j with ⟨c, hc⟩
  rw [mapEvalComplex_apply, hc]
  simp [hpz]

theorem mapEvalComplex_gram_eq_zero_of_entrywiseDvdBy
    {n κ : Type*}
    [Fintype n]
    {p : Poly}
    {z : ℂ}
    {Q : Matrix n κ Poly}
    (hpz : eval₂ (algebraMap ℝ ℂ) z p = 0)
    (hQ : EntrywiseDvdBy p (Q.transpose * Q)) :
    (mapEvalComplex z Q).transpose * mapEvalComplex z Q = 0 := by
  have hzero : mapEvalComplex z (Q.transpose * Q) = 0 :=
    mapEvalComplex_eq_zero_of_entrywiseDvdBy hpz hQ
  rw [mapEvalComplex_mul, mapEvalComplex_transpose] at hzero
  simpa using hzero

open ComplexConjugate in
theorem dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero
    {p f : Poly}
    {z : ℂ}
    (hpmap : p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)))
    (hzim : z.im ≠ 0)
    (hfz : eval₂ (algebraMap ℝ ℂ) z f = 0) :
    p ∣ f := by
  have hfroot : (f.map (algebraMap ℝ ℂ)).IsRoot z := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using hfz
  have hfconj : (f.map (algebraMap ℝ ℂ)).IsRoot (conj z) :=
    isRoot_conj_of_isRoot_map_of_real hfroot
  rcases (Polynomial.dvd_iff_isRoot.mpr hfroot) with ⟨g, hg⟩
  have hzneq : conj z ≠ z := conj_ne_self_of_im_ne_zero hzim
  have hfacne : eval (conj z) (X - C z : Polynomial ℂ) ≠ 0 := by
    simpa using (sub_ne_zero.mpr hzneq)
  have hgroot : g.IsRoot (conj z) := by
    rw [Polynomial.IsRoot] at hfconj ⊢
    rw [hg, Polynomial.eval_mul] at hfconj
    exact (mul_eq_zero.mp hfconj).resolve_left hfacne
  rcases (Polynomial.dvd_iff_isRoot.mpr hgroot) with ⟨h, hh⟩
  have hmapdvd :
      p.map (algebraMap ℝ ℂ) ∣ f.map (algebraMap ℝ ℂ) := by
    refine ⟨h, ?_⟩
    calc
      f.map (algebraMap ℝ ℂ)
          = (X - C z) * g := hg
      _ = (X - C z) * ((X - C (conj z)) * h) := by rw [hh]
      _ = ((X - C z) * (X - C (conj z))) * h := by rw [mul_assoc]
      _ = p.map (algebraMap ℝ ℂ) * h := by rw [hpmap]
  exact (Polynomial.map_dvd_map' (algebraMap ℝ ℂ)).mp hmapdvd

open ComplexConjugate in
theorem pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj
    {p a b r₁ r₂ : Poly}
    {z : ℂ}
    (hpmap : p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)))
    (hzim : z.im ≠ 0)
    (hzab : eval₂ (algebraMap ℝ ℂ) z a - Complex.I * eval₂ (algebraMap ℝ ℂ) z b = 0)
    (hzr : eval₂ (algebraMap ℝ ℂ) z r₁ + Complex.I * eval₂ (algebraMap ℝ ℂ) z r₂ = 0) :
    p ∣ a * r₁ - b * r₂ ∧
      p ∣ b * r₁ + a * r₂ := by
  have hzab' : eval₂ (algebraMap ℝ ℂ) z a = Complex.I * eval₂ (algebraMap ℝ ℂ) z b :=
    sub_eq_zero.mp hzab
  have hzr' : eval₂ (algebraMap ℝ ℂ) z r₁ = -(Complex.I * eval₂ (algebraMap ℝ ℂ) z r₂) :=
    eq_neg_of_add_eq_zero_left hzr
  have hleft :
      eval₂ (algebraMap ℝ ℂ) z (a * r₁ - b * r₂) = 0 := by
    calc
      eval₂ (algebraMap ℝ ℂ) z (a * r₁ - b * r₂)
          = eval₂ (algebraMap ℝ ℂ) z a * eval₂ (algebraMap ℝ ℂ) z r₁ -
              eval₂ (algebraMap ℝ ℂ) z b * eval₂ (algebraMap ℝ ℂ) z r₂ := by
                simp
      _ = 0 := by
            rw [hzab', hzr']
            ring_nf
            norm_num [Complex.I_sq]
  have hright :
      eval₂ (algebraMap ℝ ℂ) z (b * r₁ + a * r₂) = 0 := by
    calc
      eval₂ (algebraMap ℝ ℂ) z (b * r₁ + a * r₂)
          = eval₂ (algebraMap ℝ ℂ) z b * eval₂ (algebraMap ℝ ℂ) z r₁ +
              eval₂ (algebraMap ℝ ℂ) z a * eval₂ (algebraMap ℝ ℂ) z r₂ := by
                simp
      _ = 0 := by
            rw [hzab', hzr']
            ring_nf
  exact
    ⟨dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero hpmap hzim hleft,
      dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero hpmap hzim hright⟩

open ComplexConjugate in
theorem block_pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj
    {o κ : Type*}
    {p a b : Poly}
    {z : ℂ}
    (hpmap : p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)))
    (hzim : z.im ≠ 0)
    (hzab : eval₂ (algebraMap ℝ ℂ) z a - Complex.I * eval₂ (algebraMap ℝ ℂ) z b = 0)
    (Y : Matrix ((Unit ⊕ Unit) × o) κ Poly)
    (hYz : ∀ t j,
      eval₂ (algebraMap ℝ ℂ) z (Y (Sum.inl (), t) j) +
        Complex.I * eval₂ (algebraMap ℝ ℂ) z (Y (Sum.inr (), t) j) = 0) :
    (∀ t j, p ∣ a * Y (Sum.inl (), t) j - b * Y (Sum.inr (), t) j) ∧
      (∀ t j, p ∣ b * Y (Sum.inl (), t) j + a * Y (Sum.inr (), t) j) := by
  constructor <;> intro t j
  · exact
      (pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj hpmap hzim hzab
        (r₁ := Y (Sum.inl (), t) j) (r₂ := Y (Sum.inr (), t) j) (hYz t j)).1
  · exact
      (pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj hpmap hzim hzab
        (r₁ := Y (Sum.inl (), t) j) (r₂ := Y (Sum.inr (), t) j) (hYz t j)).2

open ComplexConjugate in
theorem row_entries_dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero
    {κ : Type*}
    {p : Poly}
    {z : ℂ}
    (hpmap : p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)))
    (hzim : z.im ≠ 0)
    (r : κ → Poly)
    (hrz : ∀ j, eval₂ (algebraMap ℝ ℂ) z (r j) = 0) :
    ∀ j, p ∣ r j := by
  intro j
  exact dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero hpmap hzim (hrz j)

open ComplexConjugate in
theorem noRealRootEvalZeroParityStatement_of_complexIsotropicRealPairBlock
    (hpair : NoRealRootStepCancellationComplexIsotropicRealPairBlockParityStatement) :
    NoRealRootEvalZeroParityStatement := by
  rcases hpair with ⟨heven, hodd⟩
  refine ⟨?_, ?_⟩
  · intro m κ p a b z hpmap hzim hzab Q hQ
    have hpz : eval₂ (algebraMap ℝ ℂ) z p = 0 := by
      have hpeval := congrArg (Polynomial.eval z) hpmap
      simpa [Polynomial.eval_map] using hpeval
    let Qz : Matrix ((Unit ⊕ Unit) × Fin m) κ ℂ := mapEvalComplex z Q
    have hQz : Qz.transpose * Qz = 0 := by
      dsimp [Qz]
      exact mapEvalComplex_gram_eq_zero_of_entrywiseDvdBy hpz hQ
    rcases heven Qz hQz with ⟨O, hOtO, hOOt, hzero⟩
    refine ⟨constPolyMat O, ?_, ?_, ?_⟩
    · simpa using congrArg constPolyMat hOtO
    · simpa using congrArg constPolyMat hOOt
    · intro t j
      have hmap :
          mapEvalComplex z (constPolyMat O * Q) =
            (O.map (algebraMap ℝ ℂ)) * Qz := by
        simp [Qz]
      have hleft :
          eval₂ (algebraMap ℝ ℂ) z ((constPolyMat O * Q) (Sum.inl (), t) j) =
            ((O.map (algebraMap ℝ ℂ)) * Qz) (Sum.inl (), t) j := by
        simpa [mapEvalComplex_apply] using
          congrArg (fun M : Matrix ((Unit ⊕ Unit) × Fin m) κ ℂ => M (Sum.inl (), t) j) hmap
      have hright :
          eval₂ (algebraMap ℝ ℂ) z ((constPolyMat O * Q) (Sum.inr (), t) j) =
            ((O.map (algebraMap ℝ ℂ)) * Qz) (Sum.inr (), t) j := by
        simpa [mapEvalComplex_apply] using
          congrArg (fun M : Matrix ((Unit ⊕ Unit) × Fin m) κ ℂ => M (Sum.inr (), t) j) hmap
      rw [hleft, hright]
      exact hzero t j
  · intro m κ p a b z hpmap hzim hzab Q hQ
    have hpz : eval₂ (algebraMap ℝ ℂ) z p = 0 := by
      have hpeval := congrArg (Polynomial.eval z) hpmap
      simpa [Polynomial.eval_map] using hpeval
    let Qz : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ :=
      mapEvalComplex z Q
    have hQz : Qz.transpose * Qz = 0 := by
      dsimp [Qz]
      exact mapEvalComplex_gram_eq_zero_of_entrywiseDvdBy hpz hQ
    rcases hodd Qz hQz with ⟨O, hOtO, hOOt, hzero, hlast⟩
    refine ⟨constPolyMat O, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg constPolyMat hOtO
    · simpa using congrArg constPolyMat hOOt
    · intro t j
      have hmap :
          mapEvalComplex z (constPolyMat O * Q) =
            (O.map (algebraMap ℝ ℂ)) * Qz := by
        simp [Qz]
      have hleft :
          eval₂ (algebraMap ℝ ℂ) z ((constPolyMat O * Q) (Sum.inl (Sum.inl (), t)) j) =
            ((O.map (algebraMap ℝ ℂ)) * Qz) (Sum.inl (Sum.inl (), t)) j := by
        simpa [mapEvalComplex_apply] using
          congrArg
            (fun M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ =>
              M (Sum.inl (Sum.inl (), t)) j) hmap
      have hright :
          eval₂ (algebraMap ℝ ℂ) z ((constPolyMat O * Q) (Sum.inl (Sum.inr (), t)) j) =
            ((O.map (algebraMap ℝ ℂ)) * Qz) (Sum.inl (Sum.inr (), t)) j := by
        simpa [mapEvalComplex_apply] using
          congrArg
            (fun M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ =>
              M (Sum.inl (Sum.inr (), t)) j) hmap
      rw [hleft, hright]
      exact hzero t j
    · intro j
      have hmap :
          mapEvalComplex z (constPolyMat O * Q) =
            (O.map (algebraMap ℝ ℂ)) * Qz := by
        simp [Qz]
      have hlast' :
          eval₂ (algebraMap ℝ ℂ) z ((constPolyMat O * Q) (Sum.inr ()) j) =
            ((O.map (algebraMap ℝ ℂ)) * Qz) (Sum.inr ()) j := by
        simpa [mapEvalComplex_apply] using
          congrArg
            (fun M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ =>
              M (Sum.inr ()) j) hmap
      rw [hlast']
      exact hlast j

open ComplexConjugate in
theorem
    noRealRootEvenBlockNormalize_of_evalZero
    (heval : NoRealRootEvenEvalZeroStatement) :
    ∀ {m : ℕ} {κ : Type}
      {p a b : Poly},
      Irreducible p →
      normalize p = p →
      (∀ x : ℝ, ¬ p.IsRoot x) →
      p = a ^ 2 + b ^ 2 →
      ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly,
        EntrywiseDvdBy p (Q.transpose * Q) →
        ∃ O : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
          O.transpose * O =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
            O * O.transpose =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
            (∀ t j,
              p ∣
                a * (O * Q) (Sum.inl (), t) j -
                  b * (O * Q) (Sum.inr (), t) j) ∧
            (∀ t j,
              p ∣
                b * (O * Q) (Sum.inl (), t) j +
                  a * (O * Q) (Sum.inr (), t) j) := by
  intro m κ p a b hp hnorm hnoroot hpab Q hQ
  rcases exists_complex_root_sub_I_mul_eq_zero_of_irreducible_of_normalized_of_forall_not_isRoot
      hp hnorm hnoroot hpab with
    ⟨z, hpmap, hzim, hzab⟩
  rcases heval hpmap hzim hzab Q hQ with ⟨O, hOtO, hOOt, hOz⟩
  have hpair :=
    block_pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj
      (p := p) (a := a) (b := b) (z := z) hpmap hzim hzab (Y := O * Q) hOz
  exact ⟨O, hOtO, hOOt, hpair.1, hpair.2⟩

open ComplexConjugate in
theorem
    noRealRootOddBlockNormalize_of_evalZero
    (heval : NoRealRootOddEvalZeroStatement) :
    ∀ {m : ℕ} {κ : Type}
      {p a b : Poly},
      Irreducible p →
      normalize p = p →
      (∀ x : ℝ, ¬ p.IsRoot x) →
      p = a ^ 2 + b ^ 2 →
      ∀ Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly,
        EntrywiseDvdBy p (Q.transpose * Q) →
        ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
            (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          O.transpose * O =
              (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
            O * O.transpose =
              (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
            (∀ t j,
              p ∣
                a * (O * Q) (Sum.inl (Sum.inl (), t)) j -
                  b * (O * Q) (Sum.inl (Sum.inr (), t)) j) ∧
            (∀ t j,
              p ∣
                b * (O * Q) (Sum.inl (Sum.inl (), t)) j +
                  a * (O * Q) (Sum.inl (Sum.inr (), t)) j) ∧
            (∀ j, p ∣ (O * Q) (Sum.inr ()) j) := by
  intro m κ p a b hp hnorm hnoroot hpab Q hQ
  rcases exists_complex_root_sub_I_mul_eq_zero_of_irreducible_of_normalized_of_forall_not_isRoot
      hp hnorm hnoroot hpab with
    ⟨z, hpmap, hzim, hzab⟩
  rcases heval hpmap hzim hzab Q hQ with ⟨O, hOtO, hOOt, hOz, hzlast⟩
  let Ytop :
      Matrix ((Unit ⊕ Unit) × Fin m) κ Poly :=
    fun i j => (O * Q) (Sum.inl i) j
  have hpair :=
    block_pair_linear_combinations_dvd_of_map_eq_mul_X_sub_C_conj
      (p := p) (a := a) (b := b) (z := z) hpmap hzim hzab (Y := Ytop)
      (by
        intro t j
        simpa [Ytop] using hOz t j)
  have hlast :
      ∀ j, p ∣ (O * Q) (Sum.inr ()) j := by
    exact
      row_entries_dvd_of_map_eq_mul_X_sub_C_conj_of_eval_eq_zero
        (p := p) (z := z) hpmap hzim
        (fun j => (O * Q) (Sum.inr ()) j) hzlast
  refine ⟨O, hOtO, hOOt, ?_, ?_, hlast⟩
  · intro t j
    simpa [Ytop] using hpair.1 t j
  · intro t j
    simpa [Ytop] using hpair.2 t j

end MatrixSOS
