/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.FullLineAlgebra.RectangularExtraction
import MatrixSOS.RationalFunction

/-!
# Algebraic identities for square extensions
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS
def squareExtension {m : ℕ} (P : PolyMat m) : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) Poly :=
  Matrix.fromBlocks
    P
    (0 : Matrix (Fin m) Unit Poly)
    (0 : Matrix Unit (Fin m) Poly)
    ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly)

@[simp] theorem squareExtension_toBlocks₁₁ {m : ℕ} (P : PolyMat m) :
    (squareExtension P).toBlocks₁₁ = P := by
  rfl

@[simp] theorem mapToFrac_squareExtension {m : ℕ} (P : PolyMat m) :
    mapToFrac (squareExtension P) =
      Matrix.fromBlocks
        (mapToFrac P)
        0
        0
        ((fun _ _ : Unit => algebraMap Poly FracPoly P.det) :
          Matrix Unit Unit FracPoly) := by
  ext i j
  cases i <;> cases j <;> simp [mapToFrac, squareExtension, Matrix.fromBlocks]

theorem posSemidef_fromBlocks_zero
    {n o : Type*}
    [Finite n] [Finite o]
    {A : Matrix n n ℝ}
    {D : Matrix o o ℝ}
    (hA : A.PosSemidef)
    (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  let _ := Fintype.ofFinite n
  let _ := Fintype.ofFinite o
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ?_
  refine ⟨Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hD.isHermitian, ?_⟩
  intro x
  rw [Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
  simpa using
    add_nonneg
      (hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
      (hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

theorem det_fromBlocks_det
    {m : ℕ}
    (P : PolyMat m) :
    (Matrix.fromBlocks
      P
      (0 : Matrix (Fin m) Unit Poly)
      (0 : Matrix Unit (Fin m) Poly)
      ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly)).det =
        P.det ^ 2 := by
  rw [Matrix.det_fromBlocks_zero₂₁ P (0 : Matrix (Fin m) Unit Poly)
    ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly)]
  rw [Matrix.det_unique ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly)]
  ring

theorem mapEval_fromBlocks_det_posSemidef
    {m : ℕ}
    (P : PolyMat m)
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∀ x : ℝ,
      (mapEval x
        (Matrix.fromBlocks
          P
          (0 : Matrix (Fin m) Unit Poly)
          (0 : Matrix Unit (Fin m) Poly)
          ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly))).PosSemidef := by
  intro x
  have hmap_det : eval x P.det = (mapEval x P).det := by
    change eval x P.det = (Matrix.map P (eval x)).det
    simpa using (RingHom.map_det (Polynomial.evalRingHom x) P)
  have hmap_blocks :
      mapEval x
          (Matrix.fromBlocks
            P
            (0 : Matrix (Fin m) Unit Poly)
            (0 : Matrix Unit (Fin m) Poly)
            ((fun _ _ : Unit => P.det) : Matrix Unit Unit Poly)) =
        Matrix.fromBlocks
          (mapEval x P)
          (0 : Matrix (Fin m) Unit ℝ)
          (0 : Matrix Unit (Fin m) ℝ)
          (mapEval x (fun _ _ : Unit => P.det)) := by
    ext i j
    cases i <;> cases j <;> simp [mapEval, Matrix.fromBlocks]
  have hdet : 0 ≤ (mapEval x P).det := Matrix.PosSemidef.det_nonneg (hP x)
  have hdet' : 0 ≤ eval x P.det := by
    simpa [hmap_det] using hdet
  have hD : (mapEval x (fun _ _ : Unit => P.det : Matrix Unit Unit Poly)).PosSemidef := by
    have hdiag :
        mapEval x (fun _ _ : Unit => P.det : Matrix Unit Unit Poly) =
          Matrix.diagonal (fun _ : Unit => eval x P.det) := by
      ext i j
      cases i
      cases j
      simp [mapEval]
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro u
    simpa using hdet'
  rw [hmap_blocks]
  simpa using
    posSemidef_fromBlocks_zero
      (A := mapEval x P)
      (D := mapEval x (fun _ _ : Unit => P.det))
      (hP x)
      hD

theorem det_squareExtension
    {m : ℕ}
    (P : PolyMat m) :
    (squareExtension P).det = P.det ^ 2 := by
  simpa [squareExtension] using det_fromBlocks_det P

theorem exists_fin_rectangular_factorization_of_squareExtension_eq_square
    {m : ℕ}
    (P : PolyMat m)
    (S : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) Poly)
    (hS : squareExtension P = S.transpose * S) :
    ∃ R : Matrix (Fin (m + 1)) (Fin m) Poly,
      P = R.transpose * R := by
  simpa [squareExtension] using
    exists_fin_rectangular_factorization_of_fromBlocks_eq_square P P.det S hS

end MatrixSOS
