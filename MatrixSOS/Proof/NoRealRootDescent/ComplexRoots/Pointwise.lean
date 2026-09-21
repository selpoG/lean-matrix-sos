/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.EvalZero
import MatrixSOS.Proof.NoRealRootDescent.Parity

/-!
# Pointwise identities for complex-root descent
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem noRealRootTwoRowBlockFactorEven_of_normalize_pointwise
    {m : ℕ}
    {κ : Type}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
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
                  a * (O * Q) (Sum.inr (), t) j))
    (Q : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly)
    (hQ : EntrywiseDvdBy p (Q.transpose * Q)) :
    ∃ O : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
      ∃ H : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
      ∃ M : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly,
        O.transpose * O =
            (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
          O * O.transpose =
            (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
          O * Q = H * M ∧
          H.transpose * H =
            p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
  rcases hnorm Q hQ with ⟨O, hOtO, hOOt, h1, h2⟩
  let Y : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly := O * Q
  rcases exists_sqAddSqBlockDiagonal_factor_of_linearCombinations_dvd
      hp0 hp Y h1 h2 with
    ⟨M, hYM⟩
  let H : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly :=
    sqAddSqBlockDiagonal (o := Fin m) a b
  have hHtH :
      H.transpose * H =
        p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
    simpa [H, sqAddSqBlockDiagonal, sqAddSqBlock, hp] using
      sqAddSqBlockDiagonal_transpose_mul (o := Fin m) a b
  refine ⟨O, H, M, hOtO, hOOt, ?_, hHtH⟩
  simpa [Y, H, sqAddSqBlockDiagonal, sqAddSqBlock] using hYM

private theorem noRealRootTwoRowBlockConstructionOdd_of_normalize_pointwise
    {m : ℕ}
    {κ : Type}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
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
            (∀ j, p ∣ (O * Q) (Sum.inr ()) j))
    (Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly)
    (hQ : EntrywiseDvdBy p (Q.transpose * Q)) :
    ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
        (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
      ∃ M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly,
        O.transpose * O =
            (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
          O * O.transpose =
            (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
          O * Q =
            sqAddSqOddUnitBlockDiagonal (o := Fin m) a b * M ∧
          (∀ j, p ∣ M (Sum.inr ()) j) := by
  rcases hnorm Q hQ with ⟨O, hOtO, hOOt, h1, h2, hbot⟩
  let Y : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly := O * Q
  rcases exists_sqAddSqOddUnitBlockDiagonal_factor_of_linearCombinations_dvd
      hp0 hp Y h1 h2 hbot with
    ⟨M₀, hYM₀, hM₀bot⟩
  exact ⟨O, M₀, hOtO, hOOt,
    by simpa [Y, sqAddSqOddUnitBlockDiagonal, sqAddSqBlockDiagonal, sqAddSqBlock] using hYM₀,
    hM₀bot⟩

theorem noRealRootTwoRowBlockFactorOdd_of_normalize_pointwise
    {m : ℕ}
    {κ : Type}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
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
            (∀ j, p ∣ (O * Q) (Sum.inr ()) j))
    (Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly)
    (hQ : EntrywiseDvdBy p (Q.transpose * Q)) :
    ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
        (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
      ∃ H : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
          (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
      ∃ M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly,
        O.transpose * O =
            (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
          O * O.transpose =
            (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
          O * Q = H * M ∧
          H.transpose * H =
            Matrix.fromBlocks
              (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
              0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) := by
  rcases noRealRootTwoRowBlockConstructionOdd_of_normalize_pointwise
      hp0 hp hnorm Q hQ with
    ⟨O, M₀, hOtO, hOOt, hOM₀, hbot⟩
  rcases exists_fromBlocks_factor_of_bottom_row_dvd (p := p) M₀ hbot with
    ⟨M, hM₀⟩
  let B : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
      (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly :=
    sqAddSqOddUnitBlockDiagonal (o := Fin m) a b
  let Punit : Matrix Unit Unit Poly := fun _ _ => p
  let P : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
      (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly :=
    Matrix.fromBlocks
      (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly)
      0 0 Punit
  let H : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
      (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly := B * P
  have hBtB :
      B.transpose * B =
        Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 (1 : Matrix Unit Unit Poly) := by
    simpa [B, hp] using sqAddSqOddUnitBlockDiagonal_transpose_mul (o := Fin m) a b
  have hHtH :
      H.transpose * H =
        Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) := by
    calc
      H.transpose * H = P.transpose * (B.transpose * B) * P := by
        simp [H, Matrix.mul_assoc]
      _ =
        P.transpose *
          Matrix.fromBlocks
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
            0 0 (1 : Matrix Unit Unit Poly) *
          P := by rw [hBtB]
        _ =
          Matrix.fromBlocks
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
            0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) := by
            dsimp [P]
            rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
            refine (Matrix.fromBlocks_inj).2 ?_
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp
            · simp
            · simp
            · apply Matrix.ext
              intro i j
              cases i
              cases j
              simp only [Matrix.transpose_zero, Matrix.mul_smul, Matrix.mul_one, smul_zero,
                Matrix.mul_zero, add_zero, mul_one, zero_add, Matrix.add_apply,
                Matrix.zero_apply]
              change (∑ x : Unit, Punit x () * Punit x ()) = p ^ 2
              simp [Punit, pow_two]
  refine ⟨O, H, M, hOtO, hOOt, ?_, hHtH⟩
  calc
    O * Q = B * M₀ := by simpa [B] using hOM₀
    _ = B * (P * M) := by rw [hM₀]
    _ = H * M := by simp [H, Matrix.mul_assoc]

theorem noRealRootEvenOneStep_of_normalize_pointwise
    {m : ℕ}
    {κ : Type}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
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
                  a * (O * Q) (Sum.inr (), t) j))
    (Q : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly)
    (hQ : EntrywiseDvdBy p (Q.transpose * Q)) :
    ∃ H : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
      ∃ U : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly,
        Q = H * U ∧
          H.transpose * H =
            p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
  rcases noRealRootTwoRowBlockFactorEven_of_normalize_pointwise
      hp0 hp hnorm Q hQ with
    ⟨O, B, U, hOtO, hOOt, hOQ, hBtB⟩
  let H : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly :=
    O.transpose * B
  refine ⟨H, U, ?_, ?_⟩
  · calc
      Q = (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) * Q := by simp
      _ = (O.transpose * O) * Q := by rw [hOtO]
      _ = O.transpose * (O * Q) := by rw [Matrix.mul_assoc]
      _ = O.transpose * (B * U) := by rw [hOQ]
      _ = O.transpose * B * U := by rw [Matrix.mul_assoc]
      _ = H * U := by simp [H]
  · calc
      H.transpose * H = B.transpose * (O * O.transpose) * B := by
        simp [H, Matrix.mul_assoc]
      _ = B.transpose * B := by rw [hOOt, Matrix.mul_one]
      _ = p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := hBtB

theorem noRealRootEvenExactFactor_of_normalize_pointwise
    {m : ℕ}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
      ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
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
                  a * (O * Q) (Sum.inr (), t) j)) :
    ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
      EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
      ∃ H U : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
        Q = H * U ∧
          H.transpose * H =
            (p ^ 2) • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
  intro Q hQ
  have hQ1 : EntrywiseDvdBy p (Q.transpose * Q) := entrywiseDvdBy_of_sq hQ
  rcases noRealRootEvenOneStep_of_normalize_pointwise
      hp0 hp hnorm Q hQ1 with
    ⟨H₀, M₁, hQM₁, hH₀tH₀⟩
  have hQeq :
      Q.transpose * Q = p • (M₁.transpose * M₁) := by
    calc
      Q.transpose * Q = (H₀ * M₁).transpose * (H₀ * M₁) := by rw [hQM₁]
      _ = M₁.transpose * (H₀.transpose * H₀) * M₁ := by
            simp [Matrix.mul_assoc]
      _ = M₁.transpose *
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly)) *
            M₁ := by rw [hH₀tH₀]
      _ = p • (M₁.transpose * M₁) := by simp
  have hM₁ : EntrywiseDvdBy p (M₁.transpose * M₁) := by
    intro i j
    have hij : p ^ 2 ∣ (Q.transpose * Q) i j := hQ i j
    have hij' : p ^ 2 ∣ (p • (M₁.transpose * M₁)) i j := by
      simpa [hQeq] using hij
    have hij'' : p * p ∣ p * ((M₁.transpose * M₁) i j) := by
      simpa [Matrix.smul_apply, pow_two, mul_assoc, mul_left_comm, mul_comm] using hij'
    exact (mul_dvd_mul_iff_left hp0).mp hij''
  rcases noRealRootEvenOneStep_of_normalize_pointwise
      hp0 hp hnorm M₁ hM₁ with
    ⟨H₁, U, hM₁U, hH₁tH₁⟩
  let H : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly := H₀ * H₁
  refine ⟨H, U, ?_, ?_⟩
  · calc
      Q = H₀ * M₁ := hQM₁
      _ = H₀ * (H₁ * U) := by rw [hM₁U]
      _ = H * U := by simp [H, Matrix.mul_assoc]
  · calc
      H.transpose * H = H₁.transpose * (H₀.transpose * H₀) * H₁ := by
        simp [H, Matrix.mul_assoc]
      _ = H₁.transpose *
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly)) *
            H₁ := by rw [hH₀tH₀]
      _ = p • (H₁.transpose * H₁) := by simp
      _ = p •
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly)) := by
        rw [hH₁tH₁]
      _ = (p ^ 2) • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
        rw [smul_smul, pow_two]

private theorem evenRowOneStep_of_normalize_pointwise
    {m : ℕ}
    {κ : Type}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (hnorm :
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
                  a * (O * Q) (Sum.inr (), t) j))
    (A : Matrix κ κ Poly)
    (T : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly)
    (hT : p • A = T.transpose * T) :
    ∃ U : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly, A = U.transpose * U := by
  have hdiv : EntrywiseDvdBy p (T.transpose * T) := by
    intro i j
    rw [← hT]
    exact dvd_mul_right p (A i j)
  rcases noRealRootEvenOneStep_of_normalize_pointwise
      hp0 hp hnorm T hdiv with
    ⟨H, U, hTU, hHtH⟩
  refine ⟨U, ?_⟩
  have hgram :
      T.transpose * T = p • (U.transpose * U) := by
    calc
      T.transpose * T = (H * U).transpose * (H * U) := by rw [hTU]
      _ = U.transpose * (H.transpose * H) * U := by simp [Matrix.mul_assoc]
      _ = U.transpose *
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly)) *
            U := by rw [hHtH]
      _ = p • (U.transpose * U) := by simp
  have hEq : p • A = p • (U.transpose * U) := by
    rw [hT, hgram]
  funext i j
  have hij := congrArg (fun M : Matrix κ κ Poly => M i j) hEq
  have hij' : p * A i j = p * (U.transpose * U) i j := by
    simpa [Matrix.smul_apply] using hij
  exact mul_left_cancel₀ hp0 hij'

theorem
    noRealRootEvenExactFactor_of_evalZero
    (heval : NoRealRootEvenEvalZeroStatement) :
    ∀ {m : ℕ}
      {p a b : Poly},
      Irreducible p →
      normalize p = p →
      (∀ x : ℝ, ¬ p.IsRoot x) →
      p = a ^ 2 + b ^ 2 →
      ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
        EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
        ∃ H U : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
          Q = H * U ∧
            H.transpose * H =
              (p ^ 2) • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) := by
  intro m p a b hp hnorm hnoroot hpab Q hQ
  rcases
    noRealRootEvenExactFactor_of_normalize_pointwise
      hp.ne_zero hpab
      (fun Q hQ =>
        noRealRootEvenBlockNormalize_of_evalZero
          heval hp hnorm hnoroot hpab Q hQ)
      Q hQ with
    ⟨H, U, hQU, hHtH⟩
  exact ⟨H, U, hQU, hHtH⟩

private def oddTopRows
    {m : ℕ}
    {κ : Type}
    (M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly) :
    Matrix ((Unit ⊕ Unit) × Fin m) κ Poly :=
  fun i j => M (Sum.inl i) j

private def oddBottomRow
    {m : ℕ}
    {κ : Type}
    (M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly) :
    Matrix Unit κ Poly :=
  fun _ j => M (Sum.inr ()) j

private theorem odd_weighted_gram_decomp
    {m : ℕ}
    {κ : Type}
    (p : Poly)
    (M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly) :
    M.transpose *
        Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
        M =
      p •
          ((oddTopRows M).transpose * oddTopRows M) +
        (p ^ 2) •
          ((oddBottomRow M).transpose * oddBottomRow M) := by
  classical
  let Mtop : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly := oddTopRows M
  let Mbot : Matrix Unit κ Poly := oddBottomRow M
  let Pbot : Matrix Unit Unit Poly := fun _ _ => p ^ 2
  have hMrows : M = Matrix.fromRows Mtop Mbot := by
    ext i j
    cases i <;> rfl
  have hMcols : M.transpose = Matrix.fromCols Mtop.transpose Mbot.transpose := by
    rw [hMrows]
    simpa using (Matrix.transpose_fromRows Mtop Mbot)
  have hBottomScale :
      Pbot * Mbot = (p ^ 2) • Mbot := by
    apply Matrix.ext
    intro i j
    cases i
    change (∑ x : Unit, p ^ 2 * Mbot x j) = p ^ 2 * Mbot () j
    simp
  have hWeightedRows :
      Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) * M =
        Matrix.fromRows (p • Mtop) ((p ^ 2) • Mbot) := by
    calc
      Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) * M =
        Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
            Matrix.fromRows Mtop Mbot := by rw [hMrows]
      _ =
        Matrix.fromRows (p • Mtop)
          (Pbot * Mbot) := by
          simpa [Mtop, Mbot] using
            (Matrix.fromBlocks_mul_fromRows
              Mtop Mbot
              (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
              0 0 Pbot)
      _ = Matrix.fromRows (p • Mtop) ((p ^ 2) • Mbot) := by rw [hBottomScale]
  calc
    M.transpose *
        Matrix.fromBlocks
          (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
          0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
        M =
      Matrix.fromCols Mtop.transpose Mbot.transpose *
        Matrix.fromRows (p • Mtop) ((p ^ 2) • Mbot) := by
        rw [Matrix.mul_assoc, hMcols, hWeightedRows]
    _ = Mtop.transpose * (p • Mtop) + Mbot.transpose * ((p ^ 2) • Mbot) := by
        simpa using
          (Matrix.fromCols_mul_fromRows
            Mtop.transpose Mbot.transpose (p • Mtop) ((p ^ 2) • Mbot))
    _ = p • (Mtop.transpose * Mtop) + (p ^ 2) • (Mbot.transpose * Mbot) := by
        simp [Matrix.mul_smul]
    _ = p • ((oddTopRows M).transpose * oddTopRows M) +
          (p ^ 2) • ((oddBottomRow M).transpose * oddBottomRow M) := by
        rfl

private theorem odd_top_gram_eq_of_sq_weighted_eq
    {m : ℕ}
    {κ : Type}
    {p : Poly}
    (hp0 : p ≠ 0)
    {A : Matrix κ κ Poly}
    {M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly}
    (h :
      (p ^ 2) • A =
        M.transpose *
          Matrix.fromBlocks
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
            0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
          M) :
    p •
        (A -
          (oddBottomRow M).transpose * oddBottomRow M) =
      (oddTopRows M).transpose * oddTopRows M := by
  classical
  let Mtop : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly := oddTopRows M
  let Mbot : Matrix Unit κ Poly := oddBottomRow M
  have hdecomp :
      (p ^ 2) • A = p • (Mtop.transpose * Mtop) + (p ^ 2) • (Mbot.transpose * Mbot) := by
    calc
      (p ^ 2) • A =
          M.transpose *
            Matrix.fromBlocks
              (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
              0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
            M := h
      _ = p • (Mtop.transpose * Mtop) + (p ^ 2) • (Mbot.transpose * Mbot) := by
          simpa [Mtop, Mbot] using odd_weighted_gram_decomp (m := m) (κ := κ) p M
  funext i j
  have hij := congrArg (fun N : Matrix κ κ Poly => N i j) hdecomp
  have hij' :
      p * p * A i j =
        p * (Mtop.transpose * Mtop) i j + p * p * (Mbot.transpose * Mbot) i j := by
    simpa [Matrix.smul_apply, Matrix.add_apply, pow_two, mul_assoc] using hij
  have hcancel :
      p * (p * (A i j - (Mbot.transpose * Mbot) i j)) =
        p * (Mtop.transpose * Mtop) i j := by
    calc
      p * (p * (A i j - (Mbot.transpose * Mbot) i j))
          = p * p * A i j - p * p * (Mbot.transpose * Mbot) i j := by ring
      _ =
          (p * (Mtop.transpose * Mtop) i j + p * p * (Mbot.transpose * Mbot) i j) -
            p * p * (Mbot.transpose * Mbot) i j := by rw [hij']
      _ = p * (Mtop.transpose * Mtop) i j := by ring
  exact mul_left_cancel₀ hp0 (by
    simpa [Matrix.smul_apply, Matrix.sub_apply, Mtop, Mbot, mul_assoc] using hcancel)

private theorem odd_fromRows_gram
    {m : ℕ}
    {κ : Type}
    (Utop : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly)
    (Ubot : Matrix Unit κ Poly) :
    (Matrix.fromRows Utop Ubot).transpose * Matrix.fromRows Utop Ubot =
      Utop.transpose * Utop + Ubot.transpose * Ubot := by
  classical
  have hcols :
      (Matrix.fromRows Utop Ubot).transpose = Matrix.fromCols Utop.transpose Ubot.transpose := by
    simpa using (Matrix.transpose_fromRows Utop Ubot)
  calc
    (Matrix.fromRows Utop Ubot).transpose * Matrix.fromRows Utop Ubot =
      Matrix.fromCols Utop.transpose Ubot.transpose * Matrix.fromRows Utop Ubot := by
        rw [hcols]
    _ = Utop.transpose * Utop + Ubot.transpose * Ubot := by
        simpa using (Matrix.fromCols_mul_fromRows Utop.transpose Ubot.transpose Utop Ubot)

theorem noRealRootOddRowOneStep_of_twoRowBlockFactor
    {m : ℕ}
    {κ : Type}
    {p : Poly}
    (hp0 : p ≠ 0)
    (hfactor :
      ∀ Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly,
        EntrywiseDvdBy p (Q.transpose * Q) →
        ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
            (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          ∃ H : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          ∃ M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly,
            O.transpose * O =
                (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                  (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
              O * O.transpose =
                (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                  (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
              O * Q = H * M ∧
              H.transpose * H =
                Matrix.fromBlocks
                  (p •
                    (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
                  0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly))
    (heven :
      ∀ (A : Matrix κ κ Poly) (T : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly),
        p • A = T.transpose * T →
        ∃ U : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly, A = U.transpose * U)
    (A : Matrix κ κ Poly)
    (T : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly)
    (hT : (p ^ 2) • A = T.transpose * T) :
    ∃ U : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly, A = U.transpose * U := by
  classical
  have hdiv : EntrywiseDvdBy p (T.transpose * T) := by
    intro i j
    rw [← hT]
    exact ⟨p * A i j, by simp [Matrix.smul_apply, pow_two, mul_assoc]⟩
  rcases hfactor T hdiv with ⟨O, H, M, hOtO, _hOOt, hOT, hHtH⟩
  let Mtop : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly := fun i j => M (Sum.inl i) j
  let Mbot : Matrix Unit κ Poly := fun _ j => M (Sum.inr ()) j
  have hweighted :
      (p ^ 2) • A =
        M.transpose *
          Matrix.fromBlocks
            (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
            0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
          M := by
    calc
      (p ^ 2) • A = T.transpose * T := hT
      _ = (O * T).transpose * (O * T) := by
        calc
          T.transpose * T =
              T.transpose *
                ((1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                    (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) * T) := by
                simp
          _ = T.transpose * ((O.transpose * O) * T) := by rw [hOtO]
          _ = (O * T).transpose * (O * T) := by simp [Matrix.mul_assoc]
      _ = (H * M).transpose * (H * M) := by rw [hOT]
      _ = M.transpose * (H.transpose * H) * M := by simp [Matrix.mul_assoc]
      _ =
          M.transpose *
            Matrix.fromBlocks
              (p • (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
              0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) *
            M := by rw [hHtH]
  have htop :
      p • (A - Mbot.transpose * Mbot) = Mtop.transpose * Mtop := by
    change
      p • (A - (oddBottomRow M).transpose * oddBottomRow M) =
        (oddTopRows M).transpose * oddTopRows M
    exact odd_top_gram_eq_of_sq_weighted_eq (m := m) (κ := κ) hp0 (A := A) (M := M) hweighted
  rcases heven (A - Mbot.transpose * Mbot) Mtop htop with ⟨Utop, hUtop⟩
  let U : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ Poly := Matrix.fromRows Utop Mbot
  refine ⟨U, ?_⟩
  calc
    A = (A - Mbot.transpose * Mbot) + Mbot.transpose * Mbot := by
      ext i j
      simp [Matrix.sub_apply, Matrix.add_apply]
    _ = Utop.transpose * Utop + Mbot.transpose * Mbot := by rw [hUtop]
    _ = U.transpose * U := by
      simpa [U] using (odd_fromRows_gram (m := m) (κ := κ) Utop Mbot).symm

theorem gram_factor_normalized_irreducible_noRoot_sqAddSq_odd_of_evalZero
    (heval : NoRealRootEvalZeroParityStatement) :
    ∀ {m : ℕ}
      {p a b : Poly},
      Irreducible p →
      normalize p = p →
      (∀ x : ℝ, ¬ p.IsRoot x) →
      p = a ^ 2 + b ^ 2 →
      ∀ Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
        EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
      ∃ U : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
          (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
        Q.transpose * Q = (p ^ 2) • (U.transpose * U) := by
  rcases heval with ⟨heven, hodd⟩
  intro m p a b hp hnorm hnoroot hpab Q hQ
  rcases (entrywiseDvdBy_iff_exists_smul (p ^ 2) (Q.transpose * Q)).mp hQ with
    ⟨A, hA⟩
  have hfactor :
      ∀ T : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
          (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
        EntrywiseDvdBy p (T.transpose * T) →
        ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
            (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          ∃ H : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          ∃ M : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
            O.transpose * O =
                (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                  (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
              O * O.transpose =
                (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                  (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly) ∧
              O * T = H * M ∧
              H.transpose * H =
                Matrix.fromBlocks
                  (p •
                    (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly))
                  0 0 ((fun _ _ : Unit => p ^ 2) : Matrix Unit Unit Poly) := by
    intro T hT
    exact
      noRealRootTwoRowBlockFactorOdd_of_normalize_pointwise hp.ne_zero hpab
        (fun T hT =>
          noRealRootOddBlockNormalize_of_evalZero
            hodd hp hnorm hnoroot hpab T hT)
        T hT
  have hevenStep :
      ∀ (A : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly)
          (T : Matrix ((Unit ⊕ Unit) × Fin m)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly),
        p • A = T.transpose * T →
        ∃ U : Matrix ((Unit ⊕ Unit) × Fin m)
              (((Unit ⊕ Unit) × Fin m) ⊕ Unit) Poly,
          A = U.transpose * U := by
    intro A T hT
    exact
      evenRowOneStep_of_normalize_pointwise hp.ne_zero hpab
        (fun T hT =>
          noRealRootEvenBlockNormalize_of_evalZero
            heven hp hnorm hnoroot hpab T hT)
        A T hT
  rcases noRealRootOddRowOneStep_of_twoRowBlockFactor hp.ne_zero hfactor hevenStep A Q hA.symm with
    ⟨U, hU⟩
  exact ⟨U, by rw [hA, hU]⟩

end MatrixSOS
