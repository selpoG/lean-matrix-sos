/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.HahnSeries.Binomial
import Mathlib.RingTheory.HahnSeries.Lex
import MatrixSOS.Proof.RationalFunction.Positivity
import MatrixSOS.Proof.OrderedExtension

/-!
Fixed Rational Hahn bridge.

The active proof spine only needs the square-root consequence that every nonnegative element of
the rational Hahn field is a square. This file proves that consequence directly by the usual
Hahn-series normalization and binomial square-root construction, then translates the fixed field
into the counterexample endpoint used by the local-global proof.
-/

open Matrix Polynomial
open scoped Matrix RatFunc
noncomputable section

namespace MatrixSOS

abbrev RationalHahnField := Lex (HahnSeries ℚ ℝ)

noncomputable def rationalHahnBinomialHalfRoot (u : HahnSeries ℚ ℝ) : HahnSeries ℚ ℝ :=
  (HahnSeries.SummableFamily.binomialFamily u ((1 : ℝ) / 2)).hsum

theorem rationalHahn_orderTopSubOnePos_pow_one (x : HahnSeries.orderTopSubOnePos ℚ ℝ) :
    x ^ (1 : ℝ) = x := by
  apply Subtype.ext
  apply Units.ext
  rw [HahnSeries.binomial_power]
  change PowerSeries.heval (x.val.val - 1) (PowerSeries.binomialSeries ℝ (1 : ℝ)) =
    x.val.val
  have hb := PowerSeries.binomialSeries_nat (R := ℝ) (A := ℝ) 1
  norm_num at hb
  rw [hb]
  change PowerSeries.heval (x.val.val - 1) (1 + PowerSeries.X) = x.val.val
  rw [map_add, PowerSeries.heval_X (x.val.val - 1) x.property]
  rw [map_one]
  simp

theorem rationalHahn_orderTopSubOnePos_sq_pow_half (x : HahnSeries.orderTopSubOnePos ℚ ℝ) :
    (x ^ ((1 : ℝ) / 2)) * (x ^ ((1 : ℝ) / 2)) = x := by
  rw [← HahnSeries.pow_add]
  rw [show (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 by ring]
  exact rationalHahn_orderTopSubOnePos_pow_one x

theorem rationalHahn_orderTopSubOnePos_pow_val_eq_hsum
    {u : HahnSeries ℚ ℝ} (hupos : 0 < (u - 1).orderTop) (r : ℝ) :
    (((HahnSeries.toOrderTopSubOnePos hupos : HahnSeries.orderTopSubOnePos ℚ ℝ) ^ r).val.val :
        HahnSeries ℚ ℝ) =
      (HahnSeries.SummableFamily.binomialFamily u r).hsum := by
  rw [HahnSeries.binomial_power]
  rfl

theorem rationalHahnBinomialHalfRoot_sq_of_orderTop_sub_one_pos
    {u : HahnSeries ℚ ℝ} (hupos : 0 < (u - 1).orderTop) :
    rationalHahnBinomialHalfRoot u * rationalHahnBinomialHalfRoot u = u := by
  let v : HahnSeries.orderTopSubOnePos ℚ ℝ := HahnSeries.toOrderTopSubOnePos hupos
  have hpow :
      (((v ^ ((1 : ℝ) / 2)).val.val : HahnSeries ℚ ℝ) =
        rationalHahnBinomialHalfRoot u) := by
    dsimp only [v, rationalHahnBinomialHalfRoot]
    exact rationalHahn_orderTopSubOnePos_pow_val_eq_hsum hupos ((1 : ℝ) / 2)
  have hv : ((v.val.val : HahnSeries ℚ ℝ) = u) := by
    dsimp only [v]
    rfl
  have hs0 : (v ^ ((1 : ℝ) / 2)) * (v ^ ((1 : ℝ) / 2)) = v :=
    rationalHahn_orderTopSubOnePos_sq_pow_half v
  have hs1 :
      ((v ^ ((1 : ℝ) / 2)).val.val : HahnSeries ℚ ℝ) *
          ((v ^ ((1 : ℝ) / 2)).val.val : HahnSeries ℚ ℝ) =
        (v.val.val : HahnSeries ℚ ℝ) := by
    have hs2 :=
      congrArg (fun w : HahnSeries.orderTopSubOnePos ℚ ℝ =>
        (w.val.val : HahnSeries ℚ ℝ)) hs0
    simpa using hs2
  rw [hpow, hv] at hs1
  exact hs1

theorem rationalHahn_isSquare_of_nonneg
    {x : RationalHahnField} (hx : 0 ≤ x) :
    IsSquare x := by
  rcases lt_or_eq_of_le hx with hxpos | hxzero
  · let s : HahnSeries ℚ ℝ := ofLex x
    have hslcpos : 0 < (ofLex x).leadingCoeff := HahnSeries.leadingCoeff_pos_iff.mpr hxpos
    have hsne : s ≠ 0 := by
      dsimp only [s]
      exact HahnSeries.leadingCoeff_ne_zero.mp hslcpos.ne'
    let γ : ℚ := s.order
    let c : ℝ := s.leadingCoeff
    let a : ℝ := Real.sqrt c
    have hslcpos' : 0 < c := by
      dsimp only [c, s]
      exact hslcpos
    have ha : c = a ^ 2 := by
      dsimp only [a]
      exact (Real.sq_sqrt hslcpos'.le).symm
    let u : HahnSeries ℚ ℝ := HahnSeries.single (-γ) c⁻¹ * s
    have hupos : 0 < (u - 1).orderTop := by
      have h1 : 0 < (1 - u).orderTop := by
        dsimp only [u, γ, c, s]
        exact HahnSeries.unit_aux (ofLex x)
          (inv_mul_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr hsne))
          (-(ofLex x).order) (neg_add_cancel (ofLex x).order)
      have hneg : u - 1 = -(1 - u) := by ring
      rw [hneg, HahnSeries.orderTop_neg]
      exact h1
    let z : HahnSeries ℚ ℝ := rationalHahnBinomialHalfRoot u
    have hzsq : z * z = u := rationalHahnBinomialHalfRoot_sq_of_orderTop_sub_one_pos hupos
    let m : HahnSeries ℚ ℝ := HahnSeries.single (γ / 2) a
    refine ⟨toLex (m * z), ?_⟩
    apply ofLex.injective
    change s = m * z * (m * z)
    have hcne : c ≠ 0 := hslcpos'.ne'
    have hdenorm : HahnSeries.single γ c * u = s := by
      dsimp only [u, γ, c, s]
      rw [← mul_assoc, HahnSeries.single_mul_single]
      rw [add_neg_cancel]
      rw [mul_inv_cancel₀ hcne]
      change (1 : HahnSeries ℚ ℝ) * ofLex x = ofLex x
      simp
    have hmm : m * m = HahnSeries.single γ c := by
      dsimp only [m, γ, c]
      rw [HahnSeries.single_mul_single]
      have hγ : γ / 2 + γ / 2 = γ := by ring
      rw [hγ]
      change HahnSeries.single γ (a * a) = HahnSeries.single γ c
      rw [show a * a = c by simpa [pow_two] using ha.symm]
    calc
      s = HahnSeries.single γ c * u := hdenorm.symm
      _ = (m * m) * (z * z) := by rw [hmm, hzsq]
      _ = m * z * (m * z) := by ring
  · refine ⟨0, ?_⟩
    rw [← hxzero]
    simp

theorem rationalHahnNonnegSquareStatement :
    ∀ {x : RationalHahnField}, 0 ≤ x → IsSquare x := by
  intro x hx
  exact rationalHahn_isSquare_of_nonneg hx

instance rationalHahnNonnegSquareClosed : NonnegSquareClosed RationalHahnField where
  isSquare_of_nonneg hx := rationalHahn_isSquare_of_nonneg hx

theorem exists_rationalHahnWitness_of_negative_real_poly_value
    {p : Poly} {x : ℝ}
    (hpx : p.eval x < 0) :
    ∃ (_ : Algebra (RatFunc ℝ) RationalHahnField),
      algebraMap (RatFunc ℝ) RationalHahnField (algebraMap Poly (RatFunc ℝ) p) < 0 := by
  let F := RatFunc ℝ
  let fAdd : ℤ →+ ℚ := Int.castAddHom ℚ
  let hfOrder : ∀ m n : ℤ, fAdd m ≤ fAdd n ↔ m ≤ n := by
    intro m n
    constructor <;> intro h
    · exact (Int.cast_le (R := ℚ)).mp h
    · exact (Int.cast_le (R := ℚ)).mpr h
  let f : ℤ ↪o ℚ :=
    { toFun := fAdd
      inj' := Int.cast_injective
      map_rel_iff' := by
        intro m n
        exact hfOrder m n }
  let ψ0 : LaurentSeries ℝ →+* HahnSeries ℚ ℝ :=
    { toFun := HahnSeries.embDomain f
      map_zero' := HahnSeries.embDomain_zero
      map_one' := HahnSeries.embDomain_one f (by rfl)
      map_add' := by
        intro a b
        exact HahnSeries.embDomain_add f a b
      map_mul' := by
        intro a b
        exact HahnSeries.embDomain_mul f (by
          intro m n
          change ((m + n : ℤ) : ℚ) = (m : ℚ) + (n : ℚ)
          exact_mod_cast rfl) a b }
  let φ0 : F →+* LaurentSeries ℝ :=
    (algebraMap F (LaurentSeries ℝ)).comp (RatFunc.laurent x).toRingHom
  let φQ0 : F →+* HahnSeries ℚ ℝ := ψ0.comp φ0
  let K := RationalHahnField
  let φQ : F →+* K :=
    { toFun := fun r => toLex (φQ0 r)
      map_zero' := by simp [φQ0]
      map_one' := by simp [φQ0]
      map_add' := by intro r s; simp [φQ0]
      map_mul' := by intro r s; simp [φQ0] }
  let : Field K := inferInstance
  let : LinearOrder K := inferInstance
  let : IsStrictOrderedRing K := inferInstance
  let : Algebra F K := RingHom.toAlgebra φQ
  have hmap :
      φ0 (algebraMap Poly F p) =
        ((((p.comp (X + C x) : Poly) : PowerSeries ℝ) : LaurentSeries ℝ)) := by
    calc
      φ0 (algebraMap Poly F p)
          = (((algebraMap Poly F (taylor x p) : F) : LaurentSeries ℝ)) := by
              exact congrArg (algebraMap F (LaurentSeries ℝ))
                  (RatFunc.laurent_algebraMap (r := x) (p := p))
      _ = ((((taylor x p : Poly) : PowerSeries ℝ) : LaurentSeries ℝ)) := by
            simpa using (RatFunc.coe_coe (F := ℝ) (P := taylor x p)).symm
      _ = ((((p.comp (X + C x) : Poly) : PowerSeries ℝ) : LaurentSeries ℝ)) := by
            simp [taylor_apply]
  have hnegQ :
      algebraMap F K (algebraMap Poly F p) < 0 := by
    change toLex (φQ0 (algebraMap Poly F p)) < 0
    rw [RingHom.comp_apply, hmap]
    let s : LaurentSeries ℝ :=
      (((p.comp (X + C x) : Poly) : PowerSeries ℝ) : LaurentSeries ℝ)
    have hnegLaurent : toLex s < 0 := by
      simpa [s] using negative_lexLaurentSeries_taylor_of_negative_real_poly_value hpx
    have hmono :=
      (HahnSeries.embDomainOrderEmbedding (R := ℝ) f).strictMono hnegLaurent
    simpa [ψ0, HahnSeries.embDomainOrderEmbedding] using hmono
  exact ⟨inferInstance, hnegQ⟩

theorem exists_rationalHahnWitnessFracPoly_of_negative_real_poly_value
    {p : Poly} {x : ℝ}
    (hpx : p.eval x < 0) :
    ∃ (_ : Algebra FracPoly RationalHahnField),
      algebraMap FracPoly RationalHahnField (algebraMap Poly FracPoly p) < 0 := by
  rcases exists_rationalHahnWitness_of_negative_real_poly_value hpx with ⟨hKAlg, hneg⟩
  let K := RationalHahnField
  let : Field K := inferInstance
  let : LinearOrder K := inferInstance
  let : IsStrictOrderedRing K := inferInstance
  let : Algebra (RatFunc ℝ) K := hKAlg
  let e : FracPoly ≃ₐ[Poly] RatFunc ℝ := FractionRing.algEquiv Poly (RatFunc ℝ)
  let : Algebra FracPoly K := RingHom.toAlgebra ((algebraMap (RatFunc ℝ) K).comp e.toRingHom)
  refine ⟨inferInstance, ?_⟩
  change algebraMap (RatFunc ℝ) K (e (algebraMap Poly FracPoly p)) < 0
  simpa using hneg

theorem fracNegativeRealPolyValueSquareClosedCounterexampleStatement_of_rationalHahnNonnegSquare :
    FracNegativeRealPolyValueSquareClosedCounterexampleStatement := by
  intro p x hpx
  rcases exists_rationalHahnWitnessFracPoly_of_negative_real_poly_value hpx with ⟨hKAlg, hneg⟩
  let K := RationalHahnField
  let : Field K := inferInstance
  let : LinearOrder K := inferInstance
  let : IsStrictOrderedRing K := inferInstance
  let : NonnegSquareClosed K := rationalHahnNonnegSquareClosed
  let : Algebra FracPoly K := hKAlg
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hneg⟩

theorem fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_rationalHahnNonnegSquare :
    FracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement := by
  exact fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_negativeRealPolyValueSquareClosedCounterexampleStatement
    fracNegativeRealPolyValueSquareClosedCounterexampleStatement_of_rationalHahnNonnegSquare


end MatrixSOS
