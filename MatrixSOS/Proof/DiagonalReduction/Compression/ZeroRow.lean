/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.Compression.SmithKernel
import MatrixSOS.Proof.DiagonalReduction.StdBasis

open Matrix Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem exists_fin_exact_factorization_of_compress_eq_and_zero_row_col
    {m ℓ : ℕ}
    (i : Fin (m + 1))
    (P : PolyMat (m + 1))
    (hrow : ∀ j, P i j = 0)
    (hcol : ∀ j, P j i = 0)
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (hR : compressPolyMat i P = R.transpose * R) :
    ∃ S : Matrix (Fin ℓ) (Fin (m + 1)) Poly,
      P = S.transpose * S := by
  refine ⟨insertMatZeroCol i R, ?_⟩
  apply eq_of_compress_eq_and_zero_row_col (i := i)
  · rw [hR]
    exact (compressPolyMat_transpose_mul_insertMatZeroCol i R).symm
  · exact hrow
  · exact hcol
  · exact transpose_mul_insertMatZeroCol_apply_same_left i R
  · exact transpose_mul_insertMatZeroCol_apply_same_right i R

theorem exists_basis_index_mulVec_zero_of_det_eq_zero
    {m : ℕ}
    (P : PolyMat m)
    (hdet : P.det = 0) :
    ∃ (o : ℕ) (b : Module.Basis (Fin o) Poly (V m)) (i : Fin o), P *ᵥ (b i) = 0 := by
  let f : V m →ₗ[Poly] V m := Matrix.toLin' P
  have hdetf : LinearMap.det f = 0 := by
    simpa [f] using (LinearMap.det_toLin' P).trans hdet
  have hker_ne : LinearMap.ker f ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hdetf
  rcases exists_smith_normal_form_for_ker f with ⟨r, o, hro, bTop, bKer, a, hsmith⟩
  have hr_fin : Module.finrank Poly (LinearMap.ker f) = r := by
    simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis bKer)
  have hr_pos : 0 < r := by
    have hfin_ne : Module.finrank Poly (LinearMap.ker f) ≠ 0 := by
      intro h0
      exact hker_ne ((Submodule.finrank_eq_zero).1 h0)
    omega
  let i0r : Fin r := ⟨0, hr_pos⟩
  let j0o : Fin o := Fin.castLE hro i0r
  have htop0 :
      ((↑(bTop j0o) : V m)) ∈ LinearMap.ker f := by
    simpa [i0r, j0o] using smith_prefix_mem_ker_of_linearMap hsmith i0r
  let bV : Module.Basis (Fin o) Poly (V m) := bTop.map (LinearEquiv.ofTop _ rfl)
  have hzero : f ((↑(bTop j0o) : V m)) = 0 := LinearMap.mem_ker.1 htop0
  refine ⟨o, bV, j0o, ?_⟩
  change f (bV j0o) = 0
  simpa [bV, j0o] using hzero

theorem bilinOfPolyMat_col_zero_of_mulVec_zero
    {m : ℕ}
    (P : PolyMat m)
    {v : V m}
    (hv : P *ᵥ v = 0) :
    ∀ z : V m, bilinOfPolyMat P z v = 0 := by
  intro z
  rw [bilin_sum_stdBasis_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hbasis : bilinOfPolyMat P (stdBasisV m i) v = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrArg (fun w => w i) hv
  simp [hbasis]

theorem bilinOfPolyMat_row_zero_of_mulVec_zero_of_isSymm
    {m : ℕ}
    (P : PolyMat m)
    (hsymm : P.IsSymm)
    {v : V m}
    (hv : P *ᵥ v = 0) :
    ∀ z : V m, bilinOfPolyMat P v z = 0 := by
  intro z
  calc
    bilinOfPolyMat P v z = bilinOfPolyMat P z v := (bilinOfPolyMat_isSymm hsymm).eq v z
    _ = 0 := bilinOfPolyMat_col_zero_of_mulVec_zero P hv z

theorem BilinForm.toMatrix_zero_row_of_eq_zero
    {R M ι : Type*}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M)
    (b : Module.Basis ι R M)
    (i0 : ι)
    (hrow : ∀ z, B (b i0) z = 0) :
    ∀ j, LinearMap.BilinForm.toMatrix b B i0 j = 0 := by
  intro j
  rw [LinearMap.BilinForm.toMatrix_apply]
  exact hrow (b j)

theorem BilinForm.toMatrix_zero_col_of_eq_zero
    {R M ι : Type*}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M)
    (b : Module.Basis ι R M)
    (i0 : ι)
    (hcol : ∀ z, B z (b i0) = 0) :
    ∀ j, LinearMap.BilinForm.toMatrix b B j i0 = 0 := by
  intro j
  rw [LinearMap.BilinForm.toMatrix_apply]
  exact hcol (b j)

theorem bilinOfPolyMat_toMatrix_zero_row_of_mulVec_zero
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (hsymm : P.IsSymm)
    (b : Module.Basis ι Poly (V m))
    (i0 : ι)
    (hvec : P *ᵥ (b i0) = 0) :
    ∀ j, LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) i0 j = 0 := by
  apply BilinForm.toMatrix_zero_row_of_eq_zero
  intro z
  exact bilinOfPolyMat_row_zero_of_mulVec_zero_of_isSymm P hsymm hvec z

theorem bilinOfPolyMat_toMatrix_zero_col_of_mulVec_zero
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (b : Module.Basis ι Poly (V m))
    (i0 : ι)
    (hvec : P *ᵥ (b i0) = 0) :
    ∀ j, LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) j i0 = 0 := by
  apply BilinForm.toMatrix_zero_col_of_eq_zero
  intro z
  exact bilinOfPolyMat_col_zero_of_mulVec_zero P hvec z

theorem exists_basis_index_toMatrix_zero_row_col_of_det_eq_zero
    {m : ℕ}
    (P : PolyMat m)
    (hsymm : P.IsSymm)
    (hdet : P.det = 0) :
    ∃ (o : ℕ) (b : Module.Basis (Fin o) Poly (V m)) (i : Fin o),
      (∀ j, LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) i j = 0) ∧
      (∀ j, LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) j i = 0) := by
  rcases exists_basis_index_mulVec_zero_of_det_eq_zero P hdet with ⟨o, b, i, hmul⟩
  refine ⟨o, b, i, ?_, ?_⟩
  · exact bilinOfPolyMat_toMatrix_zero_row_of_mulVec_zero P hsymm b i hmul
  · exact bilinOfPolyMat_toMatrix_zero_col_of_mulVec_zero P b i hmul

end MatrixSOS
