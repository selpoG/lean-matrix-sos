/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.ComplexFunctionField.RationalFunctionBridge
import MatrixSOS.Proof.RationalFunction.LocalGlobal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Values represented by the relevant Pfister forms
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section


namespace MatrixSOS

theorem fracComplexIStandardPfisterQuad4IsotropicStatement_of_complexRatFuncStandardPfisterQuad4IsotropicStatement
    (hpf : ComplexRatFuncStandardPfisterQuad4IsotropicStatement) :
    FracComplexIStandardPfisterQuad4IsotropicStatement := by
  intro u v
  let φ := fracComplexIAlgEquivComplexRatFunc
  rcases hpf (u := φ u) (v := φ v) with ⟨z, hzneq, hziso⟩
  let w : Fin 4 → FracComplexI := fun i => φ.symm (z i)
  refine ⟨w, ?_, ?_⟩
  · rcases hzneq with hz0 | hz1 | hz2 | hz3
    · exact Or.inl fun hw0 => hz0 <| by simpa [w, φ] using congrArg φ hw0
    · exact Or.inr <| Or.inl fun hw1 => hz1 <| by simpa [w, φ] using congrArg φ hw1
    · exact Or.inr <| Or.inr <| Or.inl fun hw2 => hz2 <| by
        simpa [w, φ] using congrArg φ hw2
    · exact Or.inr <| Or.inr <| Or.inr fun hw3 => hz3 <| by
        simpa [w, φ] using congrArg φ hw3
  · have hziso' := congrArg φ.symm hziso
    simpa [w, φ, Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]
      using hziso'

def FracPfister2ValueComplexIStatement : Prop :=
  ∀ {a b : FracPoly},
    a ≠ 0 →
    b ≠ 0 →
    ∃ z : Fin 4 → FracComplexI,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      pfister2ValueComplexI a b z = 0

theorem fracPfister2ValueComplexIStatement_of_complexIStandardPfisterQuad4IsotropicStatement
    (hpf : FracComplexIStandardPfisterQuad4IsotropicStatement) :
    FracPfister2ValueComplexIStatement := by
  intro a b ha0 hb0
  rcases hpf (u := algebraMap FracPoly FracComplexI a) (v := algebraMap FracPoly FracComplexI b)
      with ⟨z, hzneq, hziso⟩
  refine ⟨z, hzneq, ?_⟩
  calc
    pfister2ValueComplexI a b z
        = z 0 * z 0 + -(z 1 * algebraMap FracPoly FracComplexI a * z 1) +
            -(z 2 * algebraMap FracPoly FracComplexI b * z 2) +
              z 3 * (algebraMap FracPoly FracComplexI a * algebraMap FracPoly FracComplexI b) * z 3 := by
                simp [pfister2ValueComplexI]
                ring
    _ = 0 := by
          simpa [Matrix.toBilin'_apply, Fin.sum_univ_four] using hziso

theorem fracPfister2ValueComplexIStatement_of_complexRatFuncStandardPfisterQuad4IsotropicStatement
    (hpf : ComplexRatFuncStandardPfisterQuad4IsotropicStatement) :
    FracPfister2ValueComplexIStatement := by
  exact fracPfister2ValueComplexIStatement_of_complexIStandardPfisterQuad4IsotropicStatement
    (fracComplexIStandardPfisterQuad4IsotropicStatement_of_complexRatFuncStandardPfisterQuad4IsotropicStatement
      hpf)

theorem fracPfister2ValueComplexIStatement_of_complexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement
    (hpoly : ComplexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement) :
    FracPfister2ValueComplexIStatement := by
  exact fracPfister2ValueComplexIStatement_of_complexRatFuncStandardPfisterQuad4IsotropicStatement
    (complexRatFuncStandardPfisterQuad4IsotropicStatement_of_clearedDenominatorsStatement hpoly)

theorem fracPfister2ValueComplexIStatement_of_complexPolyDiagonalQuad4SquareDetIsotropicStatement
    (hdiag : ComplexPolyDiagonalQuad4SquareDetIsotropicStatement) :
    FracPfister2ValueComplexIStatement := by
  exact fracPfister2ValueComplexIStatement_of_complexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement
    (complexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement_of_polyDiagonalQuad4SquareDetIsotropicStatement
      hdiag)

/-- A 3-dimensional symmetric bilinear form with a prescribed nonisotropic vector admits an
orthogonal basis beginning with that vector. -/
theorem exists_orthogonal_basis_fin3_with_first
    {V : Type} [AddCommGroup V] [Module FracPoly V] [FiniteDimensional FracPoly V]
    {B : LinearMap.BilinForm FracPoly V}
    (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate)
    (hfin : Module.finrank FracPoly V = 3)
    {x : V}
    (hx : B x x ≠ 0) :
    ∃ b : Module.Basis (Fin 3) FracPoly V,
      B.IsOrthoᵢ b ∧ b 0 = x := by
  let W : Submodule FracPoly V := B.orthogonal (FracPoly ∙ x)
  have hx0 : x ≠ 0 := LinearMap.BilinForm.ne_zero_of_not_isOrtho_self x hx
  have hfinW : Module.finrank FracPoly W = 2 := by
    simpa [W, hfin, finrank_span_singleton hx0] using
      (LinearMap.BilinForm.finrank_orthogonal (B := B) hBnd (FracPoly ∙ x))
  let B' : LinearMap.BilinForm FracPoly W := B.restrict W
  have hB'symm : B'.IsSymm := hBsymm.restrict W
  have hB'nd : B'.Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hBnd hBsymm.isRefl hx
  let : Invertible (2 : FracPoly) := inferInstance
  obtain ⟨bFin, hbFin⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := B') (LinearMap.BilinForm.isSymm_iff.mp hB'symm)
  let e : Fin (Module.finrank FracPoly W) ≃ Fin 2 := finCongr hfinW
  let b₂ : Module.Basis (Fin 2) FracPoly W := bFin.reindex e
  have hb₂ : B'.IsOrthoᵢ b₂ := by
    have hbFin' := LinearMap.BilinForm.iIsOrtho_def.mp hbFin
    intro i j hij
    have hij' : e.symm i ≠ e.symm j := by
      intro hEq
      exact hij (e.symm.injective hEq)
    simpa [b₂, Module.Basis.reindex] using hbFin' (e.symm i) (e.symm j) hij'
  let b : Module.Basis (Fin 3) FracPoly V :=
    Module.Basis.mkFinCons x b₂
      (by
        intro d z hz hdz
        rw [add_eq_zero_iff_neg_eq] at hdz
        rw [← hdz, Submodule.neg_mem_iff] at hz
        have hdisj := (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := B) hx).disjoint
        rw [Submodule.disjoint_def] at hdisj
        have hzero := hdisj (d • x)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) hz
        exact (smul_eq_zero.mp hzero).resolve_right fun hd => hx <| hd.symm ▸ map_zero _)
      (by
        intro z
        refine ⟨-B x z / B x x, ?_⟩
        intro w hw
        rcases Submodule.mem_span_singleton.mp hw with ⟨d, rfl⟩
        have hxx0 : B x x ≠ 0 := by
          simpa using hx
        calc
          B (d • x) (z + (-B x z / B x x) • x)
              = d * (B x z + (-B x z / B x x) * B x x) := by
                  simp [smul_eq_mul, mul_add]
          _ = 0 := by
                field_simp [hxx0]
                ring)
  have hb : B.IsOrthoᵢ b := by
    rw [Module.Basis.coe_mkFinCons]
    intro j i
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      intro hij <;> simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    · exact (hij rfl).elim
    · have hxj : B x ((b₂ j : W) : V) = 0 :=
        (b₂ j).prop _ (Submodule.mem_span_singleton_self x)
      change B ((b₂ j : W) : V) x = 0
      exact hBsymm.eq_iff.mp hxj
    · change B x ((b₂ i : W) : V) = 0
      exact (b₂ i).prop _ (Submodule.mem_span_singleton_self x)
    · change B' (b₂ j) (b₂ i) = 0
      exact (LinearMap.BilinForm.iIsOrtho_def.mp hb₂) j i (ne_of_apply_ne _ hij)
  refine ⟨b, hb, ?_⟩
  rw [Module.Basis.coe_mkFinCons]
  rfl

theorem isOrtho_fin4_basis_of_orthogonal_tail
    {B : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly)}
    (hBsymm : B.IsSymm)
    {x : Fin 4 → FracPoly}
    {W : Submodule FracPoly (Fin 4 → FracPoly)}
    {bW : Module.Basis (Fin 3) FracPoly W}
    (hbW : (B.restrict W).IsOrthoᵢ bW)
    (hW : ∀ i : Fin 3, B x ((bW i : W) : Fin 4 → FracPoly) = 0)
    (b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly))
    (hb0 : b 0 = x)
    (hbsucc : ∀ i : Fin 3, b (Fin.succ i) = ((bW i : W) : Fin 4 → FracPoly)) :
    B.IsOrthoᵢ b := by
  rw [LinearMap.isOrthoᵢ_def]
  intro i j hij
  revert j
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j hij
    revert hij
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      exact (hij rfl).elim
    · intro hij
      rw [hb0, hbsucc j]
      exact hW j
  · intro j hij
    revert hij
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      rw [hb0, hbsucc i]
      exact hBsymm.eq_iff.mp (hW i)
    · intro hij
      rw [hbsucc i, hbsucc j]
      change (B.restrict W) (bW i) (bW j) = 0
      exact (LinearMap.isOrthoᵢ_def.mp hbW) i j
        (fun h => hij (by cases h; rfl))

-- A 4-dimensional symmetric bilinear form with a prescribed orthogonal pair of equal nonzero
-- norms admits an orthogonal basis beginning with that pair.
theorem exists_orthogonal_basis_fin4_of_pair
    {B : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly)}
    (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate)
    {x y : Fin 4 → FracPoly}
    {c : FracPoly}
    (hxy : B x y = 0)
    (hxx : B x x = c)
    (hyy : B y y = c)
    (hc0 : c ≠ 0) :
    ∃ b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly),
      B.IsOrthoᵢ b ∧ b 0 = x ∧ b 1 = y := by
  let W₁ : Submodule FracPoly (Fin 4 → FracPoly) := B.orthogonal (FracPoly ∙ x)
  have hx : B x x ≠ 0 := by
    simpa [hxx] using hc0
  have hx0 : x ≠ 0 := LinearMap.BilinForm.ne_zero_of_not_isOrtho_self x hx
  have hyW₁ : y ∈ W₁ := by
    intro z hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨d, rfl⟩
    change B (d • x) y = 0
    simp [hxy]
  let y₁ : W₁ := ⟨y, hyW₁⟩
  let B₁ : LinearMap.BilinForm FracPoly W₁ := B.restrict W₁
  have hB₁symm : B₁.IsSymm := hBsymm.restrict W₁
  have hB₁nd : B₁.Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hBnd hBsymm.isRefl hx
  have hy₁ : B₁ y₁ y₁ ≠ 0 := by
    intro hy₁
    have hyy0 : B y y = 0 := by
      simpa [B₁, y₁] using hy₁
    exact hc0 (hyy.symm.trans hyy0)
  have hfinW₁ : Module.finrank FracPoly W₁ = 3 := by
    simpa [W₁, finrank_span_singleton hx0, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (LinearMap.BilinForm.finrank_orthogonal (B := B) hBnd (FracPoly ∙ x))
  obtain ⟨b₁, hb₁, hb₁0⟩ := exists_orthogonal_basis_fin3_with_first
    (V := W₁) (B := B₁) hB₁symm hB₁nd hfinW₁ hy₁
  let b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly) :=
    Module.Basis.mkFinCons x b₁
      (by
        intro d z hz hdz
        rw [add_eq_zero_iff_neg_eq] at hdz
        rw [← hdz, Submodule.neg_mem_iff] at hz
        have hdisj := (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := B) hx).disjoint
        rw [Submodule.disjoint_def] at hdisj
        have hzero := hdisj (d • x)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) hz
        exact (smul_eq_zero.mp hzero).resolve_right fun hd => hx <| hd.symm ▸ map_zero _)
      (by
        intro z
        refine ⟨-B x z / B x x, ?_⟩
        intro w hw
        rcases Submodule.mem_span_singleton.mp hw with ⟨d, rfl⟩
        have hxx0 : B x x ≠ 0 := by
          simpa using hx
        calc
          B (d • x) (z + (-B x z / B x x) • x)
              = d * (B x z + (-B x z / B x x) * B x x) := by
                  simp [smul_eq_mul, mul_add]
          _ = 0 := by
                field_simp [hxx0]
                ring)
  have hW₁ : ∀ i : Fin 3, B x ((b₁ i : W₁) : Fin 4 → FracPoly) = 0 := by
    intro i
    exact (b₁ i).prop _ (Submodule.mem_span_singleton_self x)
  have hb0 : b 0 = x := by
    rw [Module.Basis.coe_mkFinCons]
    rfl
  have hbsucc : ∀ i : Fin 3, b (Fin.succ i) = ((b₁ i : W₁) : Fin 4 → FracPoly) := by
    intro i
    rw [Module.Basis.coe_mkFinCons]
    rfl
  have hb : B.IsOrthoᵢ b :=
    isOrtho_fin4_basis_of_orthogonal_tail hBsymm hb₁ hW₁ b hb0 hbsucc
  refine ⟨b, hb, ?_, ?_⟩
  · rw [Module.Basis.coe_mkFinCons]
    rfl
  · rw [Module.Basis.coe_mkFinCons]
    change ((b₁ 0 : W₁) : Fin 4 → FracPoly) = y
    exact congrArg Subtype.val hb₁0

/-- The previous orthogonal-basis lemma diagonalizes the bilinear form to a matrix of the shape
`diag(c, c, d, e)`. This is the immediate algebraic output used before the square-determinant
descent equalizes the last two slots. -/
theorem exists_diagonal_basis_fin4_of_pair
    {B : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly)}
    (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate)
    {x y : Fin 4 → FracPoly}
    {c : FracPoly}
    (hxy : B x y = 0)
    (hxx : B x x = c)
    (hyy : B y y = c)
    (hc0 : c ≠ 0) :
    ∃ b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly), ∃ d e : FracPoly,
      b 0 = x ∧
      b 1 = y ∧
      LinearMap.BilinForm.toMatrix b B = Matrix.diagonal ![c, c, d, e] := by
  obtain ⟨b, hb, hb0, hb1⟩ := exists_orthogonal_basis_fin4_of_pair
    hBsymm hBnd hxy hxx hyy hc0
  refine ⟨b, B (b 2) (b 2), B (b 3) (b 3), hb0, hb1, ?_⟩
  have hb' := LinearMap.BilinForm.iIsOrtho_def.mp hb
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i
    · simpa [hb0, LinearMap.BilinForm.toMatrix_apply] using hxx
    · simpa [hb1, LinearMap.BilinForm.toMatrix_apply] using hyy
    · simp [LinearMap.BilinForm.toMatrix_apply]
    · simp [LinearMap.BilinForm.toMatrix_apply]
  · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal, hij] using hb' i j hij

/-- If the determinant square-class of a `4`-dimensional bilinear form is trivial, the diagonal
form produced from an orthogonal pair of equal nonzero norms has the remaining two slots whose
product is a square. This is the determinant step before equalizing those slots to reach the
`⟨c,c,d,d⟩` shape. -/
theorem exists_diagonal_basis_fin4_of_pair_of_isSquare_det
    {B : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly)}
    (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate)
    {x y : Fin 4 → FracPoly}
    {c : FracPoly}
    (hxy : B x y = 0)
    (hxx : B x x = c)
    (hyy : B y y = c)
    (hc0 : c ≠ 0)
    (hdet : IsSquare ((LinearMap.BilinForm.toMatrix (Pi.basisFun FracPoly (Fin 4)) B).det)) :
    ∃ b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly), ∃ d e : FracPoly,
      b 0 = x ∧
      b 1 = y ∧
      LinearMap.BilinForm.toMatrix b B = Matrix.diagonal ![c, c, d, e] ∧
      IsSquare (d * e) := by
  obtain ⟨b, d, e, hb0, hb1, hdiag⟩ := exists_diagonal_basis_fin4_of_pair
    hBsymm hBnd hxy hxx hyy hc0
  have hdet' : IsSquare ((LinearMap.BilinForm.toMatrix b B).det) := by
    let e₀ : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly) := Pi.basisFun FracPoly (Fin 4)
    have hmat := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := e₀) (c := b) (B := B)
    rw [← hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      IsSquare.mul hdet (IsSquare.sq ((e₀.toMatrix b).det))
  have hsqde : IsSquare (d * e) := by
    rcases hdet' with ⟨r, hr⟩
    rw [hdiag, Matrix.det_diagonal] at hr
    have hprod : c * c * (d * e) = r * r := by
      simpa [Fin.prod_univ_four, mul_assoc, mul_left_comm, mul_comm] using hr
    have hc02 : c * c ≠ 0 := mul_ne_zero hc0 hc0
    have hdiv : d * e = (r * r) / (c * c) := by
      apply (eq_div_iff hc02).2
      calc
        (d * e) * (c * c) = c * c * (d * e) := by ring
        _ = r * r := hprod
    refine ⟨r / c, ?_⟩
    calc
      d * e = (r * r) / (c * c) := hdiv
      _ = r / c * (r / c) := by
            field_simp [hc0]
  exact ⟨b, d, e, hb0, hb1, hdiag, hsqde⟩

/-- If a `4`-dimensional regular bilinear form has a prescribed orthogonal pair of equal nonzero
norms and square determinant, then after a final basis rescaling it diagonalizes to
`diag(c, c, d, d)`. This packages the square-determinant descent needed in the ternary/Pfister
route. -/
theorem exists_ccdd_basis_fin4_of_pair_of_isSquare_det
    {B : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly)}
    (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate)
    {x y : Fin 4 → FracPoly}
    {c : FracPoly}
    (hxy : B x y = 0)
    (hxx : B x x = c)
    (hyy : B y y = c)
    (hc0 : c ≠ 0)
    (hdet : IsSquare ((LinearMap.BilinForm.toMatrix (Pi.basisFun FracPoly (Fin 4)) B).det)) :
    ∃ b : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly), ∃ d : FracPoly,
      b 0 = x ∧
      b 1 = y ∧
      LinearMap.BilinForm.toMatrix b B = Matrix.diagonal ![c, c, d, d] := by
  obtain ⟨b, d, e, hb0, hb1, hdiag, hsqde⟩ := exists_diagonal_basis_fin4_of_pair_of_isSquare_det
    hBsymm hBnd hxy hxx hyy hc0 hdet
  have hdetnz : ((LinearMap.BilinForm.toMatrix b B).det) ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hBnd
  rw [hdiag, Matrix.det_diagonal] at hdetnz
  have hprod_ne : c * c * (d * e) ≠ 0 := by
    simpa [Fin.prod_univ_four, mul_assoc, mul_left_comm, mul_comm] using hdetnz
  have hde0 : d * e ≠ 0 := by
    intro hde0
    apply hprod_ne
    simp [hde0]
  have hd0 : d ≠ 0 := fun hd => hde0 <| by simp [hd]
  obtain ⟨r, hr⟩ := hsqde
  have hr0 : r ≠ 0 := by
    intro hr0
    apply hde0
    rw [hr, hr0]
    simp
  let w : Fin 4 → FracPolyˣ := fun i =>
    if h : i = 3 then Units.mk0 (d / r) (div_ne_zero hd0 hr0) else 1
  let b' : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly) := b.unitsSMul w
  have hb'0 : b' 0 = x := by
    simp [b', w, Module.Basis.unitsSMul_apply, hb0]
  have hb'1 : b' 1 = y := by
    simp [b', w, Module.Basis.unitsSMul_apply, hb1]
  have heq : e = d * ((r / d) * (r / d)) := by
    field_simp [hd0]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr
  have hmat := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) (c := b') (B := B)
  refine ⟨b', d, hb'0, hb'1, ?_⟩
  rw [← hmat, hdiag, Module.Basis.toMatrix_unitsSMul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w, heq, Matrix.mul_apply, Fin.sum_univ_four]
  field_simp [hd0, hr0]

/-- Specialized `⟨c,c,d,d⟩` reduction for the associated Pfister form `⟨1,-a,-b,ab⟩`. Once an
orthogonal pair of equal nonzero norms is extracted, the remaining determinant work is automatic
because the determinant of `pfister2Matrix a b` is already a square. -/
theorem exists_ccdd_basis_fin4_of_pfister2_pair
    {a b c : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    {x y : Fin 4 → FracPoly}
    (hxy : pfister2Bilin a b x y = 0)
    (hxx : pfister2Bilin a b x x = c)
    (hyy : pfister2Bilin a b y y = c)
    (hc0 : c ≠ 0) :
    ∃ e : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly), ∃ d : FracPoly,
      e 0 = x ∧
      e 1 = y ∧
      LinearMap.BilinForm.toMatrix e (pfister2Bilin a b) = Matrix.diagonal ![c, c, d, d] := by
  exact exists_ccdd_basis_fin4_of_pair_of_isSquare_det
    (pfister2Bilin_isSymm a b)
    (pfister2Bilin_nondegenerate ha0 hb0)
    hxy hxx hyy hc0
    (isSquare_pfister2Bilin_det a b)

/-- Once the associated Pfister form `⟨1,-a,-b,ab⟩` has been diagonalized to `⟨c,c,d,d⟩`,
an explicit representation `-cd = u² + v²` produces a global isotropic vector for the ternary
subform `⟨1,-a,-b⟩`. This packages the easy final transport step after the hard
complex/diagonal reduction work. -/
theorem exists_ternary_isotropic_of_pfister2_ccdd_and_neg_mul_sum_two_squares
    {a b c d : FracPoly}
    (hc0 : c ≠ 0)
    (hccdd :
      ∃ e : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly),
        LinearMap.BilinForm.toMatrix e (pfister2Bilin a b) = Matrix.diagonal ![c, c, d, d])
    (hsq : ∃ u v : FracPoly, -c * d = u ^ 2 + v ^ 2) :
    ∃ x y z : FracPoly, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2 := by
  rcases hccdd with ⟨e, hdiag⟩
  rcases hsq with ⟨u, v, huv⟩
  rcases exists_ccdd_isotropic_of_neg_mul_sum_two_squares (c := c) (d := d) hc0 huv with
    ⟨x, y, z, w, hneq, hsum⟩
  let q : Fin 4 → FracPoly := ![x, y, z, w]
  let v : Fin 4 → FracPoly := e.equivFun.symm q
  have hvpf :
      ∃ x y z w : FracPoly,
        (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
        x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * w ^ 2 = 0 := by
    refine ⟨v 0, v 1, v 2, v 3, ?_, ?_⟩
    · by_contra hv0
      push Not at hv0
      rcases hv0 with ⟨hv00, hv01, hv02, hv03⟩
      have hvzero : v = 0 := by
        ext i
        fin_cases i <;> simp [hv00, hv01, hv02, hv03]
      have hq0 : q = 0 := by
        calc
          q = e.equivFun v := by
                simpa [v] using (e.equivFun.apply_symm_apply q).symm
          _ = 0 := by simp [hvzero]
      have hx0 : x = 0 := by simpa [q] using congrFun hq0 0
      have hy0 : y = 0 := by simpa [q] using congrFun hq0 1
      have hz0 : z = 0 := by simpa [q] using congrFun hq0 2
      have hw0 : w = 0 := by simpa [q] using congrFun hq0 3
      rcases hneq with hx | hy | hz | hw
      · exact hx hx0
      · exact hy hy0
      · exact hz hz0
      · exact hw hw0
    · calc
        v 0 ^ 2 - a * v 1 ^ 2 - b * v 2 ^ 2 + a * b * v 3 ^ 2
            = pfister2Bilin a b v v := by
                rw [pfister2Bilin_apply]
                ring
        _ = Matrix.toBilin e (LinearMap.BilinForm.toMatrix e (pfister2Bilin a b)) v v := by
              rw [Matrix.toBilin_toMatrix]
        _ = Matrix.toBilin e (Matrix.diagonal ![c, c, d, d]) v v := by rw [hdiag]
        _ = c * x ^ 2 + c * y ^ 2 + d * z ^ 2 + d * w ^ 2 := by
              simp [Matrix.toBilin_apply, v, q, Matrix.diagonal, Fin.sum_univ_four,
                e.equivFun_symm_apply]
              ring
        _ = 0 := hsum
  exact exists_ternary_isotropic_of_exists_pfister2_isotropic hvpf
theorem fracCCDDPlainIsotropicOverSquareClosedExtensions_of_pfister2_diagonal
    {a b c d : FracPoly}
    (hlocal : FracPfister2PlainIsotropicOverSquareClosedExtensions a b)
    (hdiag :
      ∃ e : Module.Basis (Fin 4) FracPoly (Fin 4 → FracPoly),
        LinearMap.BilinForm.toMatrix e (pfister2Bilin a b) = Matrix.diagonal ![c, c, d, d]) :
    FracCCDDPlainIsotropicOverSquareClosedExtensions c d := by
  intro K _ _ _ _ _
  rcases hlocal (K := K) with ⟨x₀, y₀, z₀, w₀, hneq, hpf⟩
  rcases hdiag with ⟨e, hdiagE⟩
  let P : Matrix (Fin 4) (Fin 4) FracPoly := (Pi.basisFun FracPoly (Fin 4)).toMatrix e
  let Q : Matrix (Fin 4) (Fin 4) FracPoly := e.toMatrix (Pi.basisFun FracPoly (Fin 4))
  let PK : Matrix (Fin 4) (Fin 4) K := P.map (algebraMap FracPoly K)
  let QK : Matrix (Fin 4) (Fin 4) K := Q.map (algebraMap FracPoly K)
  let MK : Matrix (Fin 4) (Fin 4) K := (pfister2Matrix a b).map (algebraMap FracPoly K)
  let DK : Matrix (Fin 4) (Fin 4) K := (Matrix.diagonal ![c, c, d, d]).map (algebraMap FracPoly K)
  have hPKQK : PK * QK = 1 := by
    calc
      PK * QK = (P * Q).map (algebraMap FracPoly K) := by
        simp [PK, QK, Matrix.map_mul]
      _ = (1 : Matrix (Fin 4) (Fin 4) FracPoly).map (algebraMap FracPoly K) := by
        rw [(Pi.basisFun FracPoly (Fin 4)).toMatrix_mul_toMatrix_flip e]
      _ = 1 := by simp
  let : Invertible PK.det := Matrix.detInvertibleOfRightInverse PK QK hPKQK
  let : Invertible PK := Matrix.invertibleOfDetInvertible PK
  have hdiagP :
      Pᵀ * pfister2Matrix a b * P = Matrix.diagonal ![c, c, d, d] := by
    rw [← hdiagE]
    simpa [P, LinearMap.BilinForm.toMatrix_basisFun, pfister2Bilin_toMatrix'] using
      (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
        (b := Pi.basisFun FracPoly (Fin 4)) (c := e) (B := pfister2Bilin a b))
  have hdiagPK :
      PKᵀ * MK * PK = DK := by
    simpa [PK, MK, DK, Matrix.map_mul, Matrix.transpose_map] using congrArg
      (fun M : Matrix (Fin 4) (Fin 4) FracPoly => M.map (algebraMap FracPoly K)) hdiagP
  let q : Fin 4 → K := ![x₀, y₀, z₀, w₀]
  have hqpf0 :
      x₀ * x₀ + -(y₀ * algebraMap FracPoly K a * y₀) + -(z₀ * algebraMap FracPoly K b * z₀) +
          w₀ * (algebraMap FracPoly K a * algebraMap FracPoly K b) * w₀ = 0 := by
    calc
      x₀ * x₀ + -(y₀ * algebraMap FracPoly K a * y₀) + -(z₀ * algebraMap FracPoly K b * z₀) +
          w₀ * (algebraMap FracPoly K a * algebraMap FracPoly K b) * w₀
          =
          x₀ ^ 2 - (algebraMap FracPoly K a) * y₀ ^ 2 - (algebraMap FracPoly K b) * z₀ ^ 2 +
            (algebraMap FracPoly K a) * (algebraMap FracPoly K b) * w₀ ^ 2 := by
              ring
      _ = 0 := hpf
  have hqpf : Matrix.toBilin' MK q q = 0 := by
    simpa [q, MK, pfister2Matrix, Matrix.toBilin'_apply, Fin.sum_univ_four] using hqpf0
  have hqnonzero : q ≠ 0 := by
    intro hq0
    rcases hneq with hx | hy | hz | hw
    · exact hx (by simpa [q] using congrFun hq0 0)
    · exact hy (by simpa [q] using congrFun hq0 1)
    · exact hz (by simpa [q] using congrFun hq0 2)
    · exact hw (by simpa [q] using congrFun hq0 3)
  let r : Fin 4 → K := PK⁻¹.mulVec q
  have hqeq : q = PK.mulVec r := by
    calc
      q = (1 : Matrix (Fin 4) (Fin 4) K).mulVec q := by simp
      _ = (PK * PK⁻¹).mulVec q := by
            rw [Matrix.mul_nonsing_inv (A := PK) (isUnit_of_invertible PK.det)]
      _ = PK.mulVec (PK⁻¹.mulVec q) := by rw [Matrix.mulVec_mulVec]
      _ = PK.mulVec r := by rfl
  have hrnonzero : r ≠ 0 := by
    intro hr0
    apply hqnonzero
    rw [hqeq, hr0]
    simp
  have hdiagIso :
      Matrix.toBilin' DK r r = 0 := by
    have hcomp :
        Matrix.toBilin' MK (PK.mulVec r) (PK.mulVec r) = Matrix.toBilin' DK r r := by
      simpa [LinearMap.BilinForm.comp_apply, hdiagPK] using
        congrArg (fun B => B r r) (Matrix.toBilin'_comp MK PK PK)
    have hqpf' : Matrix.toBilin' MK (PK.mulVec r) (PK.mulVec r) = 0 := by
      simpa [hqeq] using hqpf
    exact hcomp.symm.trans hqpf'
  refine ⟨r 0, r 1, r 2, r 3, ?_, ?_⟩
  · by_contra hr0
    push Not at hr0
    apply hrnonzero
    ext i
    fin_cases i
    · simpa [r] using hr0.1
    · simpa [r] using hr0.2.1
    · simpa [r] using hr0.2.2.1
    · simpa [r] using hr0.2.2.2
  · have hdiagIso' :
        algebraMap FracPoly K c * r 0 ^ 2 + algebraMap FracPoly K c * r 1 ^ 2 +
          algebraMap FracPoly K d * r 2 ^ 2 + algebraMap FracPoly K d * r 3 ^ 2 = 0 := by
      have hdiagIso0 :
          r 0 * algebraMap FracPoly K c * r 0 + r 1 * algebraMap FracPoly K c * r 1 +
            r 2 * algebraMap FracPoly K d * r 2 + r 3 * algebraMap FracPoly K d * r 3 = 0 := by
        simpa [DK, Matrix.toBilin'_apply, Fin.sum_univ_four] using hdiagIso
      calc
        algebraMap FracPoly K c * r 0 ^ 2 + algebraMap FracPoly K c * r 1 ^ 2 +
            algebraMap FracPoly K d * r 2 ^ 2 + algebraMap FracPoly K d * r 3 ^ 2
            =
            r 0 * algebraMap FracPoly K c * r 0 + r 1 * algebraMap FracPoly K c * r 1 +
              r 2 * algebraMap FracPoly K d * r 2 + r 3 * algebraMap FracPoly K d * r 3 := by
                ring
        _ = 0 := hdiagIso0
    exact hdiagIso'

theorem fracTernaryIsotropicSquareClosedLocalGlobalStatement_of_complexI_and_ccddSqAddSqStatement
    (hcomplex : FracPfister2ValueComplexIStatement)
    (hccddsq : FracCCDDPlainIsotropicOverSquareClosedExtensionsSqAddSqStatement) :
    FracTernaryIsotropicSquareClosedLocalGlobalStatement := by
  intro a b ha0 hb0 hlocal
  rcases hcomplex ha0 hb0 with ⟨z, hzneq, hziso⟩
  rcases exists_ternary_isotropic_or_pfister2_pair_of_exists_pfister2ValueComplexI_zero
      ⟨z, hzneq, hziso⟩ with hter | hpair
  · exact hter
  · rcases hpair with ⟨x, y, c, hxy, hxx, hyy, hc0⟩
    rcases exists_ccdd_basis_fin4_of_pfister2_pair ha0 hb0 hxy hxx hyy hc0 with ⟨e, d, _, _, hdiag⟩
    have hpfLocal : FracPfister2PlainIsotropicOverSquareClosedExtensions a b :=
      (fracPfister2PlainIsotropicOverSquareClosedExtensions_iff_ternary).mpr hlocal
    have hccddLocal : FracCCDDPlainIsotropicOverSquareClosedExtensions c d :=
      fracCCDDPlainIsotropicOverSquareClosedExtensions_of_pfister2_diagonal hpfLocal ⟨e, hdiag⟩
    have hdetnz : (Matrix.diagonal ![c, c, d, d]).det ≠ 0 := by
      rw [← hdiag]
      exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).mp
        (pfister2Bilin_nondegenerate ha0 hb0)
    have hd0 : d ≠ 0 := by
      intro hd0
      apply hdetnz
      simp [Matrix.det_diagonal, Fin.prod_univ_four, hd0]
    rcases hccddsq hc0 hd0 hccddLocal with ⟨u, v, huv⟩
    exact exists_ternary_isotropic_of_pfister2_ccdd_and_neg_mul_sum_two_squares
      hc0 ⟨e, hdiag⟩ ⟨u, v, huv⟩

theorem fracTernaryIsotropicSquareClosedLocalGlobalStatement_of_complexI_and_ccddNonnegWhereDefinedStatement
    (hcomplex : FracPfister2ValueComplexIStatement)
    (hccddnonneg : FracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement) :
    FracTernaryIsotropicSquareClosedLocalGlobalStatement := by
  exact fracTernaryIsotropicSquareClosedLocalGlobalStatement_of_complexI_and_ccddSqAddSqStatement
    hcomplex
    (fracCCDDPlainIsotropicOverSquareClosedExtensionsSqAddSqStatement_of_ccddNonnegWhereDefinedStatement
      hccddnonneg)
end MatrixSOS
