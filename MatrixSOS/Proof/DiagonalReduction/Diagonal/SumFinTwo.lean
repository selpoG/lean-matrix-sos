/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.Diagonal.Reindex
import MatrixSOS.Proof.DiagonalReduction.BinaryMatrix

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem exists_rat_factorization_of_diagonal_sumFinTwo_step
    (hstmt : FracBinaryRepresentsOneStatement)
    {m : Type*}
    [Fintype m]
    [DecidableEq m]
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b)
    (d : m → FracPoly)
    (hD : ∃ R : Matrix (Unit ⊕ m) (Unit ⊕ m) FracPoly,
      Matrix.diagonal (Sum.elim (fun _ : Unit => a * b) d) = R.transpose * R) :
    ∃ S : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly,
      Matrix.diagonal (Sum.elim (fun i : Fin 2 => ![a, b] i) d) = S.transpose * S := by
  classical
  let : DecidableEq (Fin 2 ⊕ m) := inferInstance
  let : DecidableEq (Unit ⊕ m) := inferInstance
  let : DecidableEq (Unit ⊕ (Unit ⊕ m)) := inferInstance
  let e : Fin 2 ⊕ m ≃ Unit ⊕ (Unit ⊕ m) :=
    { toFun := fun i =>
        match i with
        | Sum.inl j =>
            if h : j = 0 then Sum.inl ()
            else Sum.inr (Sum.inl ())
        | Sum.inr j => Sum.inr (Sum.inr j)
      invFun := fun i =>
        match i with
        | Sum.inl _ => Sum.inl 0
        | Sum.inr (Sum.inl _) => Sum.inl 1
        | Sum.inr (Sum.inr j) => Sum.inr j
      left_inv := by
        intro i
        cases i with
        | inl i =>
            fin_cases i
            · simp
            · simp
        | inr j =>
            simp
      right_inv := by
        intro i
        cases i with
        | inl u =>
            simp
        | inr i =>
            cases i with
            | inl u =>
                simp
            | inr j =>
                simp }
  have hdiagOneMul : Matrix.diagonal ![1, a * b] = !![1, 0; 0, a * b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hdiagAB : Matrix.diagonal ![a, b] = !![a, 0; 0, b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hOne :
      ∃ T : Matrix (Unit ⊕ (Unit ⊕ m)) (Unit ⊕ (Unit ⊕ m)) FracPoly,
        Matrix.diagonal
            (Sum.elim (fun _ : Unit => (1 : FracPoly))
              (Sum.elim (fun _ : Unit => a * b) d)) =
          T.transpose * T := by
    exact exists_rat_factorization_of_diagonal_sum_one
      (Sum.elim (fun _ : Unit => a * b) d) hD
  have hBlock :
      ∃ T : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly,
        Matrix.diagonal (fun i => Sum.elim (fun _ : Unit => (1 : FracPoly))
          (Sum.elim (fun _ : Unit => a * b) d) (e i)) =
          T.transpose * T := by
    exact exists_rat_factorization_of_diagonal_reindex e hOne
  have hBlock' :
      ∃ T : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly,
        Matrix.fromBlocks !![1, 0; 0, a * b] 0 0 (Matrix.diagonal d) = T.transpose * T := by
    rcases hBlock with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    calc
      Matrix.fromBlocks !![1, 0; 0, a * b] 0 0 (Matrix.diagonal d)
          = Matrix.fromBlocks (Matrix.diagonal ![1, a * b]) 0 0 (Matrix.diagonal d) := by
              simp [hdiagOneMul]
      _ = Matrix.diagonal (Sum.elim (fun i : Fin 2 => ![1, a * b] i) d) := by
            symm
            exact diagonal_sumElim_eq_fromBlocks ![1, a * b] d
      _ = Matrix.diagonal (fun i => Sum.elim (fun _ : Unit => (1 : FracPoly))
            (Sum.elim (fun _ : Unit => a * b) d) (e i)) := by
            congr 1
            ext i
            cases i with
            | inl i =>
                fin_cases i <;> simp [e]
            | inr j =>
                simp [e]
      _ = T.transpose * T := hT
  rcases exists_rat_factorization_of_fromBlocks_binaryReduction hstmt ha0 hb0 ha hb
      (Matrix.diagonal d) hBlock' with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  calc
    Matrix.diagonal (Sum.elim (fun i : Fin 2 => ![a, b] i) d)
        = Matrix.fromBlocks (Matrix.diagonal ![a, b]) 0 0 (Matrix.diagonal d) := by
            exact diagonal_sumElim_eq_fromBlocks ![a, b] d
    _ = Matrix.fromBlocks !![a, 0; 0, b] 0 0 (Matrix.diagonal d) := by
          simp [hdiagAB]
    _ = S.transpose * S := hS

end MatrixSOS
