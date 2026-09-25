/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.NoRealRootDescent.Divisibility

/-!
# Statements of the parity descent identities
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

def sumUnitUnitEquivFinTwo : Unit ⊕ Unit ≃ Fin 2 :=
  (Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv

def sqAddSqEvenEquiv (m : ℕ) : ((Unit ⊕ Unit) × Fin m) ≃ Fin (2 * m) :=
  (Equiv.prodCongr sumUnitUnitEquivFinTwo (Equiv.refl _)).trans finProdFinEquiv

def sqAddSqOddEquiv (m : ℕ) : (((Unit ⊕ Unit) × Fin m) ⊕ Unit) ≃ Fin (2 * m + 1) :=
  ((sqAddSqEvenEquiv m).sumCongr finOneEquiv.symm).trans
    (finSumFinEquiv : Fin (2 * m) ⊕ Fin 1 ≃ Fin (2 * m + 1))

def NoRealRootStepCancellationComplexIsotropicRealPairBlockEvenStatement : Prop :=
  ∀ {m : ℕ} {κ : Type},
      ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) κ ℂ,
        Q.transpose * Q = 0 →
        ∃ O : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) ℝ,
          O.transpose * O =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) ℝ) ∧
            O * O.transpose =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) ℝ) ∧
            (∀ t j,
              ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (), t) j +
                Complex.I * ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inr (), t) j = 0)

def NoRealRootStepCancellationComplexIsotropicRealPairBlockOddStatement : Prop :=
  ∀ {m : ℕ} {κ : Type},
      ∀ Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ,
        Q.transpose * Q = 0 →
        ∃ O : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
            (((Unit ⊕ Unit) × Fin m) ⊕ Unit) ℝ,
          O.transpose * O =
              (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                (((Unit ⊕ Unit) × Fin m) ⊕ Unit) ℝ) ∧
            O * O.transpose =
              (1 : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
                (((Unit ⊕ Unit) × Fin m) ⊕ Unit) ℝ) ∧
            (∀ t j,
              ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inl (), t)) j +
                Complex.I * ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inr (), t)) j = 0) ∧
            (∀ j, ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inr ()) j = 0)

def NoRealRootStepCancellationComplexIsotropicRealPairBlockParityStatement : Prop :=
  NoRealRootStepCancellationComplexIsotropicRealPairBlockEvenStatement ∧
    NoRealRootStepCancellationComplexIsotropicRealPairBlockOddStatement

def NoRealRootEvenEvalZeroStatement : Prop :=
  ∀ {m : ℕ} {κ : Type}
      {p a b : Poly}
      {z : ℂ},
      p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (star z)) →
      z.im ≠ 0 →
      eval₂ (algebraMap ℝ ℂ) z a - Complex.I * eval₂ (algebraMap ℝ ℂ) z b = 0 →
      ∀ Q : Matrix ((Unit ⊕ Unit) × Fin m) κ Poly,
        EntrywiseDvdBy p (Q.transpose * Q) →
        ∃ O : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly,
          O.transpose * O =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
            O * O.transpose =
              (1 : Matrix ((Unit ⊕ Unit) × Fin m) ((Unit ⊕ Unit) × Fin m) Poly) ∧
            (∀ t j,
              eval₂ (algebraMap ℝ ℂ) z ((O * Q) (Sum.inl (), t) j) +
                Complex.I * eval₂ (algebraMap ℝ ℂ) z ((O * Q) (Sum.inr (), t) j) = 0)

def NoRealRootOddEvalZeroStatement : Prop :=
  ∀ {m : ℕ} {κ : Type}
      {p a b : Poly}
      {z : ℂ},
      p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (star z)) →
      z.im ≠ 0 →
      eval₂ (algebraMap ℝ ℂ) z a - Complex.I * eval₂ (algebraMap ℝ ℂ) z b = 0 →
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
              eval₂ (algebraMap ℝ ℂ) z ((O * Q) (Sum.inl (Sum.inl (), t)) j) +
                Complex.I * eval₂ (algebraMap ℝ ℂ) z ((O * Q) (Sum.inl (Sum.inr (), t)) j) = 0) ∧
            (∀ j, eval₂ (algebraMap ℝ ℂ) z ((O * Q) (Sum.inr ()) j) = 0)

def NoRealRootEvalZeroParityStatement : Prop :=
  NoRealRootEvenEvalZeroStatement ∧
    NoRealRootOddEvalZeroStatement

end MatrixSOS
