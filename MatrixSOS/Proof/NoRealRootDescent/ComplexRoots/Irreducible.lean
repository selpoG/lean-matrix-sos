/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.Pointwise

/-!
# Descent through irreducible factors with no real roots
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem gram_factor_of_normalized_irreducible_noRoot_sqAddSq
    {n : Type*}
    [Fintype n]
    {p a b : Poly}
    (hp : Irreducible p)
    (hnorm : normalize p = p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a)
    (hpab : p = a ^ 2 + b ^ 2)
    (Q : Matrix n n Poly)
    (hQ : EntrywiseDvdBy (p ^ 2) (Q.transpose * Q)) :
    ∃ U : Matrix n n Poly,
      Q.transpose * Q = (p ^ 2) • (U.transpose * U) := by
  classical
  let heval :=
    noRealRootEvalZeroParityStatement_of_complexIsotropicRealPairBlock
      noRealRootStepCancellationComplexIsotropicRealPairBlockParityStatement_theorem
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let Qfin : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) Poly :=
    Matrix.reindex e e Q
  have hQQfin :
      Matrix.reindex e e (Q.transpose * Q) = Qfin.transpose * Qfin := by
    dsimp [Qfin]
    exact (Matrix.reindexLinearEquiv_mul Poly Poly e e e Q.transpose Q).symm
  have hQfin : EntrywiseDvdBy (p ^ 2) (Qfin.transpose * Qfin) := by
    intro i j
    rw [← hQQfin]
    simpa [Qfin, Matrix.reindex_apply] using hQ (e.symm i) (e.symm j)
  have hfin :
      ∃ Ufin : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) Poly,
        Qfin.transpose * Qfin = (p ^ 2) • (Ufin.transpose * Ufin) := by
    rcases Nat.even_or_odd' (Fintype.card n) with ⟨k, hcard | hcard⟩
    · let eEven : ((Unit ⊕ Unit) × Fin k) ≃ Fin (2 * k) := sqAddSqEvenEquiv k
      let eCard : Fin (Fintype.card n) ≃ Fin (2 * k) := finCongr hcard
      let ePar : Fin (Fintype.card n) ≃ ((Unit ⊕ Unit) × Fin k) := eCard.trans eEven.symm
      let Qpar : Matrix ((Unit ⊕ Unit) × Fin k) ((Unit ⊕ Unit) × Fin k) Poly :=
        Matrix.reindex ePar ePar Qfin
      have hQQpar :
          Matrix.reindex ePar ePar (Qfin.transpose * Qfin) =
            Qpar.transpose * Qpar := by
        dsimp [Qpar]
        exact
          (Matrix.reindexLinearEquiv_mul Poly Poly ePar ePar ePar
            Qfin.transpose Qfin).symm
      have hQpar : EntrywiseDvdBy (p ^ 2) (Qpar.transpose * Qpar) := by
        intro i j
        rw [← hQQpar]
        simpa [Qpar, Matrix.reindex_apply] using hQfin (ePar.symm i) (ePar.symm j)
      rcases
        noRealRootEvenExactFactor_of_evalZero
          heval.1 hp hnorm hnoroot hpab Qpar hQpar with
        ⟨Hpar, Upar, hQHU, hHtH⟩
      let Ufin : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) Poly :=
        Matrix.reindex ePar.symm ePar.symm Upar
      refine ⟨Ufin, ?_⟩
      have hparGram :
          Qpar.transpose * Qpar = (p ^ 2) • (Upar.transpose * Upar) := by
        calc
          Qpar.transpose * Qpar = (Hpar * Upar).transpose * (Hpar * Upar) := by rw [hQHU]
          _ = Upar.transpose * (Hpar.transpose * Hpar) * Upar := by simp [Matrix.mul_assoc]
          _ =
              Upar.transpose *
                ((p ^ 2) •
                  (1 : Matrix ((Unit ⊕ Unit) × Fin k) ((Unit ⊕ Unit) × Fin k) Poly)) *
                Upar := by rw [hHtH]
          _ = (p ^ 2) • (Upar.transpose * Upar) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
              simp
      have hmul :
          Matrix.reindex ePar.symm ePar.symm (Upar.transpose * Upar) = Ufin.transpose * Ufin := by
        dsimp [Ufin]
        exact
          (Matrix.reindexLinearEquiv_mul Poly Poly ePar.symm ePar.symm ePar.symm Upar.transpose Upar).symm
      calc
        Qfin.transpose * Qfin = Matrix.reindex ePar.symm ePar.symm (Qpar.transpose * Qpar) := by
          rw [← hQQpar]
          ext i j
          simp [Matrix.reindex_apply]
        _ = Matrix.reindex ePar.symm ePar.symm ((p ^ 2) • (Upar.transpose * Upar)) := by
          rw [hparGram]
        _ = (p ^ 2) • (Ufin.transpose * Ufin) := by
          ext i j
          simp [Ufin, Matrix.reindex_apply, Matrix.smul_apply]
    · let eOdd : (((Unit ⊕ Unit) × Fin k) ⊕ Unit) ≃ Fin (2 * k + 1) := sqAddSqOddEquiv k
      let eCard : Fin (Fintype.card n) ≃ Fin (2 * k + 1) := finCongr hcard
      let ePar : Fin (Fintype.card n) ≃ (((Unit ⊕ Unit) × Fin k) ⊕ Unit) :=
        eCard.trans eOdd.symm
      let Qpar : Matrix (((Unit ⊕ Unit) × Fin k) ⊕ Unit) (((Unit ⊕ Unit) × Fin k) ⊕ Unit) Poly :=
        Matrix.reindex ePar ePar Qfin
      have hQQpar :
          Matrix.reindex ePar ePar (Qfin.transpose * Qfin) =
            Qpar.transpose * Qpar := by
        dsimp [Qpar]
        exact
          (Matrix.reindexLinearEquiv_mul Poly Poly ePar ePar ePar
            Qfin.transpose Qfin).symm
      have hQpar : EntrywiseDvdBy (p ^ 2) (Qpar.transpose * Qpar) := by
        intro i j
        rw [← hQQpar]
        simpa [Qpar, Matrix.reindex_apply] using hQfin (ePar.symm i) (ePar.symm j)
      rcases
        gram_factor_normalized_irreducible_noRoot_sqAddSq_odd_of_evalZero
          heval hp hnorm hnoroot hpab Qpar hQpar with
        ⟨Upar, hparGram⟩
      let Ufin : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) Poly :=
        Matrix.reindex ePar.symm ePar.symm Upar
      refine ⟨Ufin, ?_⟩
      have hmul :
          Matrix.reindex ePar.symm ePar.symm (Upar.transpose * Upar) = Ufin.transpose * Ufin := by
        dsimp [Ufin]
        exact
          (Matrix.reindexLinearEquiv_mul Poly Poly ePar.symm ePar.symm ePar.symm Upar.transpose Upar).symm
      calc
        Qfin.transpose * Qfin = Matrix.reindex ePar.symm ePar.symm (Qpar.transpose * Qpar) := by
          rw [← hQQpar]
          ext i j
          simp [Matrix.reindex_apply]
        _ = Matrix.reindex ePar.symm ePar.symm ((p ^ 2) • (Upar.transpose * Upar)) := by
          rw [hparGram]
        _ = (p ^ 2) • (Ufin.transpose * Ufin) := by
          ext i j
          simp [Ufin, Matrix.reindex_apply, Matrix.smul_apply]
  rcases hfin with ⟨Ufin, hUfin⟩
  let U : Matrix n n Poly := Matrix.reindex e.symm e.symm Ufin
  refine ⟨U, ?_⟩
  have hmul :
      Matrix.reindex e.symm e.symm (Ufin.transpose * Ufin) = U.transpose * U := by
    dsimp [U]
    exact (Matrix.reindexLinearEquiv_mul Poly Poly e.symm e.symm e.symm Ufin.transpose Ufin).symm
  calc
    Q.transpose * Q = Matrix.reindex e.symm e.symm (Qfin.transpose * Qfin) := by
      rw [← hQQfin]
      ext i j
      simp [Matrix.reindex_apply]
    _ = Matrix.reindex e.symm e.symm ((p ^ 2) • (Ufin.transpose * Ufin)) := by
      rw [hUfin]
    _ = (p ^ 2) • (U.transpose * U) := by
      ext i j
      simp [U, Matrix.reindex_apply, Matrix.smul_apply]

end MatrixSOS
