/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz

/-!
# Projective ideal height bounds for homogeneous equations
-/

noncomputable section

namespace MatrixSOS

/-- Height of the irrelevant maximal ideal `(X_i)` in a finite polynomial ring.

This is the commutative-algebra endpoint used by the Tsen/projective route after reducing the
projective dimension-count theorem to affine Nullstellensatz and Krull's height theorem. -/
def MvPolynomialIdealOfVarsHeightStatement (K : Type) [Field K] : Prop :=
  ∀ {ι : Type} [Fintype ι],
    (MvPolynomial.idealOfVars ι K).height = Fintype.card ι

theorem vanishingIdeal_singleton_zero_eq_idealOfVars
    {K ι : Type} [Field K] :
    MvPolynomial.vanishingIdeal K ({(0 : ι → K)} : Set (ι → K)) =
      MvPolynomial.idealOfVars ι K := by
  ext p
  constructor
  · intro hp
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hp
    rw [MvPolynomial.idealOfVars_eq_restrictSupportIdeal]
    simp only [MvPolynomial.restrictSupportIdeal]
    intro m hm
    refine Nat.pos_iff_ne_zero.mpr ?_
    intro hmdeg
    have hm0 : m = 0 := by
      simpa [Finsupp.degree_eq_zero_iff] using hmdeg
    exact (MvPolynomial.mem_support_iff.mp hm) (by
      rw [hm0]
      simpa [MvPolynomial.aeval_zero, MvPolynomial.constantCoeff_eq] using hp)
  · intro hp
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    rw [MvPolynomial.idealOfVars_eq_restrictSupportIdeal] at hp
    simp only [MvPolynomial.restrictSupportIdeal] at hp
    have hcoeff : p.coeff 0 = 0 := by
      by_cases h0 : p.coeff 0 = 0
      · exact h0
      · have hmem : (0 : ι →₀ ℕ) ∈ p.support := by
          simpa [Finsupp.mem_support_iff] using h0
        have hdeg := hp hmem
        simp at hdeg
    simpa [MvPolynomial.aeval_zero, MvPolynomial.constantCoeff_eq] using hcoeff

theorem mvPolynomial_mem_idealOfVars_iff_constantCoeff_eq_zero
    {σ R : Type*} [CommRing R] (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.idealOfVars σ R ↔ MvPolynomial.constantCoeff p = 0 := by
  rw [← pow_one (MvPolynomial.idealOfVars σ R),
    MvPolynomial.mem_pow_idealOfVars_iff' (σ := σ) (R := R) 1 p]
  rw [MvPolynomial.constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp [Finsupp.degree])
  · intro h m hm
    have hm0 : m = 0 :=
      (Finsupp.degree_eq_zero_iff m).mp (Nat.lt_one_iff.mp hm)
    simpa [hm0] using h

private theorem optionEquivLeft_symm_C
    {σ R : Type*} [CommSemiring R] (q : MvPolynomial σ R) :
    (MvPolynomial.optionEquivLeft R σ).symm (Polynomial.C q) =
      MvPolynomial.rename Option.some q := by
  apply (MvPolynomial.optionEquivLeft R σ).injective
  have hhom :
      (MvPolynomial.optionEquivLeft R σ).toRingEquiv.toRingHom.comp
          (MvPolynomial.rename (R := R) (Option.some : σ → Option σ)).toRingHom =
        Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.optionEquivLeft_C]
    · intro i
      simp [MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some]
  rw [AlgEquiv.apply_symm_apply]
  exact (RingHom.congr_fun hhom q).symm

private theorem ideal_mem_map_equiv_iff_symm_mem
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) (I : Ideal R) (x : S) :
    x ∈ I.map e ↔ e.symm x ∈ I := by
  constructor
  · intro hx
    change x ∈ I.map (e : R →+* S) at hx
    rw [Ideal.mem_map_iff_of_surjective (f := (e : R →+* S)) (I := I) e.surjective] at hx
    rcases hx with ⟨y, hy, hyx⟩
    simpa [← hyx] using hy
  · intro hx
    change x ∈ I.map (e : R →+* S)
    simpa using (Ideal.mem_map_of_mem (e : R →+* S) hx)

private theorem option_idealOfVars_under_eq (K σ : Type) [CommRing K] :
    ((MvPolynomial.idealOfVars (Option σ) K).map
        (MvPolynomial.optionEquivLeft K σ).toRingEquiv).under (MvPolynomial σ K) =
      MvPolynomial.idealOfVars σ K := by
  ext q
  change Polynomial.C q ∈ (MvPolynomial.idealOfVars (Option σ) K).map
      (MvPolynomial.optionEquivLeft K σ).toRingEquiv ↔ q ∈ MvPolynomial.idealOfVars σ K
  rw [ideal_mem_map_equiv_iff_symm_mem]
  rw [mvPolynomial_mem_idealOfVars_iff_constantCoeff_eq_zero,
    mvPolynomial_mem_idealOfVars_iff_constantCoeff_eq_zero]
  change MvPolynomial.constantCoeff
      ((MvPolynomial.optionEquivLeft K σ).symm (Polynomial.C q)) = 0 ↔
    MvPolynomial.constantCoeff q = 0
  rw [optionEquivLeft_symm_C, MvPolynomial.constantCoeff_rename]

theorem idealOfVars_isMaximal (K σ : Type) [Field K] :
    (MvPolynomial.idealOfVars σ K).IsMaximal := by
  have hker :
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K) =
        MvPolynomial.idealOfVars σ K := by
    ext p
    rw [RingHom.mem_ker]
    exact (mvPolynomial_mem_idealOfVars_iff_constantCoeff_eq_zero p).symm
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K)
    (fun x => ⟨MvPolynomial.C x, by simp⟩)

theorem ideal_height_radical {R : Type*} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  simp [Ideal.height, Ideal.radical_minimalPrimes]

private theorem option_idealOfVars_height
    (K σ : Type) [Field K] [Finite σ]
    (IH : (MvPolynomial.idealOfVars σ K).height = Nat.card σ) :
    (MvPolynomial.idealOfVars (Option σ) K).height = Nat.card (Option σ) := by
  let e := (MvPolynomial.optionEquivLeft K σ).toRingEquiv
  let P : Ideal (Polynomial (MvPolynomial σ K)) :=
    (MvPolynomial.idealOfVars (Option σ) K).map e
  have hPmax : P.IsMaximal := by
    dsimp [P]
    have hmax : (MvPolynomial.idealOfVars (Option σ) K).IsMaximal :=
      idealOfVars_isMaximal K (Option σ)
    exact Ideal.map_isMaximal_of_equiv e
  have hPlies : P.LiesOver (MvPolynomial.idealOfVars σ K) := by
    refine ⟨?_⟩
    dsimp [P, e]
    exact (option_idealOfVars_under_eq K σ).symm
  have hstep :
      P.height = (MvPolynomial.idealOfVars σ K).height + 1 :=
    @Polynomial.height_eq_height_add_one (MvPolynomial σ K) _ _
      (MvPolynomial.idealOfVars σ K) P hPmax hPlies
  have hmap :
      P.height = (MvPolynomial.idealOfVars (Option σ) K).height := by
    dsimp [P]
    rw [RingEquiv.height_map]
  calc
    (MvPolynomial.idealOfVars (Option σ) K).height = P.height := hmap.symm
    _ = (MvPolynomial.idealOfVars σ K).height + 1 := hstep
    _ = Nat.card σ + 1 := by rw [IH]
    _ = Nat.card (Option σ) := by simp

private theorem renameEquiv_idealOfVars_map
    {K σ τ : Type} [CommRing K] (e : σ ≃ τ) :
    (MvPolynomial.idealOfVars σ K).map (MvPolynomial.renameEquiv K e).toRingEquiv =
      MvPolynomial.idealOfVars τ K := by
  rw [MvPolynomial.idealOfVars, MvPolynomial.idealOfVars]
  apply le_antisymm
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨e i, by simp⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hx : MvPolynomial.X (e.symm j) ∈
        Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) :=
      Ideal.subset_span ⟨e.symm j, rfl⟩
    have hmap := Ideal.mem_map_of_mem (MvPolynomial.renameEquiv K e).toRingEquiv hx
    simpa using hmap

theorem idealOfVars_height_natCard
    {K ι : Type} [Field K] [Finite ι] :
    (MvPolynomial.idealOfVars ι K).height = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
      rw [← renameEquiv_idealOfVars_map (e := e)]
      rw [RingEquiv.height_map]
      rw [H]
      exact congrArg Nat.cast (Nat.card_congr e)
  | h_empty =>
      rw [show MvPolynomial.idealOfVars PEmpty K = (⊥ : Ideal (MvPolynomial PEmpty K)) by
        rw [MvPolynomial.idealOfVars]
        apply le_antisymm
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          cases i
        · exact bot_le]
      simp
  | h_option IH =>
      exact option_idealOfVars_height K _ IH

theorem idealOfVars_height_fintype
    {K ι : Type} [Field K] [Fintype ι] :
    (MvPolynomial.idealOfVars ι K).height = Fintype.card ι := by
  simpa [Nat.card_eq_fintype_card] using
    (idealOfVars_height_natCard (K := K) (ι := ι))

theorem mvPolynomialIdealOfVarsHeightStatement_theorem
    (K : Type) [Field K] :
    MvPolynomialIdealOfVarsHeightStatement K := by
  intro ι hι
  exact idealOfVars_height_fintype (K := K) (ι := ι)

end MatrixSOS
