/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.NoRealRootDescent.Parity.BlockFactorization
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Parity decomposition in descent without real roots
-/

open Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

def sqAddSqBlock
    {α : Type*}
    [Zero α]
    [Neg α]
    (a b : α) :
    Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α :=
  Matrix.fromBlocks
    (fun _ _ : Unit => a)
    (fun _ _ : Unit => b)
    (fun _ _ : Unit => -b)
    (fun _ _ : Unit => a)

def sqAddSqBlockDiagonal
    {o α : Type*}
    [Fintype o]
    [DecidableEq o]
    [Zero α]
    [Neg α]
    (a b : α) :
    Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α :=
  Matrix.blockDiagonal (fun _ : o => sqAddSqBlock a b)

def sqAddSqOddUnitBlockDiagonal
    {o α : Type*}
    [Fintype o]
    [DecidableEq o]
    [Zero α]
    [Neg α]
    [One α]
    (a b : α) :
    Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) (((Unit ⊕ Unit) × o) ⊕ Unit) α :=
  Matrix.fromBlocks (sqAddSqBlockDiagonal (o := o) a b) 0 0 1

theorem sqAddSqOddUnitBlockDiagonal_transpose_mul
    {o α : Type*}
    [Fintype o]
    [DecidableEq o]
    [CommRing α]
      (a b : α) :
      (sqAddSqOddUnitBlockDiagonal (o := o) a b).transpose *
          sqAddSqOddUnitBlockDiagonal (o := o) a b =
        Matrix.fromBlocks
          ((a ^ 2 + b ^ 2) •
            (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α))
          0 0 (1 : Matrix Unit Unit α) := by
    simpa [sqAddSqOddUnitBlockDiagonal, sqAddSqBlockDiagonal, sqAddSqBlock] using
      sqAddSqOddUnitBlockDiagonal_transpose_mul_explicit (o := o) a b

theorem exists_fromBlocks_factor_of_bottom_row_dvd
    {n κ : Type*}
    [Fintype n]
    [DecidableEq n]
    {p : Poly}
    (Y : Matrix (n ⊕ Unit) κ Poly)
    (hY : ∀ j, p ∣ Y (Sum.inr ()) j) :
    ∃ M : Matrix (n ⊕ Unit) κ Poly,
      Y =
        Matrix.fromBlocks (1 : Matrix n n Poly) 0 0 ((fun _ _ : Unit => p) : Matrix Unit Unit Poly) *
          M := by
    classical
    let Y₁ : Matrix n κ Poly := fun i j => Y (Sum.inl i) j
    let m : κ → Poly := fun j => Classical.choose (hY j)
    let Y₂ : Matrix Unit κ Poly := fun _ j => m j
    let P : Matrix Unit Unit Poly := fun _ _ => p
    let M : Matrix (n ⊕ Unit) κ Poly := Matrix.fromRows Y₁ Y₂
    have hDM :=
      Matrix.fromBlocks_mul_fromRows Y₁ Y₂ (1 : Matrix n n Poly)
        (0 : Matrix n Unit Poly) (0 : Matrix Unit n Poly) P
    refine ⟨M, ?_⟩
    apply Matrix.ext
    intro i j
    cases i with
    | inl i =>
        have htop :
            (Matrix.fromBlocks (1 : Matrix n n Poly) 0 0
                ((fun _ _ : Unit => p) : Matrix Unit Unit Poly) * M) (Sum.inl i) j =
              Y (Sum.inl i) j := by
          calc
            (Matrix.fromBlocks (1 : Matrix n n Poly) 0 0
                ((fun _ _ : Unit => p) : Matrix Unit Unit Poly) * M) (Sum.inl i) j
                = (Sum.elim ((1 : Matrix n n Poly) * Y₁) (P * Y₂) (Sum.inl i)) j := by
                    simpa [M, Matrix.fromRows, P] using
                      congrArg (fun N : Matrix (n ⊕ Unit) κ Poly => N (Sum.inl i) j) hDM
            _ = ((1 : Matrix n n Poly) * Y₁) i j := rfl
            _ = Y₁ i j := by
                  exact congrArg (fun N : Matrix n κ Poly => N i j) (Matrix.one_mul Y₁)
            _ = Y (Sum.inl i) j := rfl
        exact htop.symm
    | inr i =>
        have hm : Y (Sum.inr ()) j = p * m j := Classical.choose_spec (hY j)
        have hbot :
            (Matrix.fromBlocks (1 : Matrix n n Poly) 0 0
                ((fun _ _ : Unit => p) : Matrix Unit Unit Poly) * M) (Sum.inr i) j =
              Y (Sum.inr i) j := by
          calc
            (Matrix.fromBlocks (1 : Matrix n n Poly) 0 0
                ((fun _ _ : Unit => p) : Matrix Unit Unit Poly) * M) (Sum.inr i) j =
              (Sum.elim ((1 : Matrix n n Poly) * Y₁) (P * Y₂) (Sum.inr i)) j := by
                simpa [M, Matrix.fromRows, P] using
                  congrArg (fun N : Matrix (n ⊕ Unit) κ Poly => N (Sum.inr i) j) hDM
            _ = (P * Y₂) i j := rfl
            _ = p * m j := by
              cases i
              change (∑ x : Unit, p * m j) = p * m j
              simp
            _ = Y (Sum.inr ()) j := hm.symm
            _ = Y (Sum.inr i) j := rfl
        exact hbot.symm


end MatrixSOS
