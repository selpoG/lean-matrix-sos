/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.ProjectiveIdealHeight
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective common zeros for the proof of Tsen's theorem
-/

noncomputable section

namespace MatrixSOS

/-- Homogeneous-polynomial version of the projective dimension-count theorem over an
algebraically closed field. The equations may have different positive degrees. -/
def ProjectiveHomogeneousDimensionStatement (K : Type) [Field K] : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
    Fintype.card κ < Fintype.card ι →
    ∀ P : κ → MvPolynomial ι K,
      (∀ k : κ, ∃ d : ℕ, 0 < d ∧ (P k).IsHomogeneous d) →
      ∃ x : ι → K,
        (∃ i : ι, x i ≠ 0) ∧
        ∀ k : κ, MvPolynomial.eval x (P k) = 0

/--
The standard `C₁`-field statement: every positive-degree homogeneous polynomial
in more variables than its degree has a nontrivial zero.
-/
def C1FieldStatement (K : Type) [Field K] : Prop :=
  ∀ {ι : Type} [Fintype ι],
    ∀ d : ℕ, 0 < d →
      d < Fintype.card ι →
      ∀ P : MvPolynomial ι K,
        P.IsHomogeneous d →
        ∃ x : ι → K,
          (∃ i : ι, x i ≠ 0) ∧
          MvPolynomial.eval x P = 0

private theorem projectiveHomogeneousDimensionStatement_of_idealOfVarsHeightStatement
    {K : Type} [Field K] [IsAlgClosed K]
    (hheight : MvPolynomialIdealOfVarsHeightStatement K) :
    ProjectiveHomogeneousDimensionStatement K := by
  classical
  intro ι κ _hι _hκ hcard P hhom
  by_contra hno
  push Not at hno
  let I : Ideal (MvPolynomial ι K) := Ideal.span (Set.range P)
  have hzero_mem : (0 : ι → K) ∈ MvPolynomial.zeroLocus K I := by
    rw [MvPolynomial.zeroLocus_span]
    intro p hp
    rcases hp with ⟨k, rfl⟩
    rcases hhom k with ⟨d, hdpos, hP⟩
    have hcoeff : MvPolynomial.constantCoeff (P k) = 0 := by
      rw [MvPolynomial.constantCoeff_eq]
      exact hP.coeff_eq_zero (ne_of_lt hdpos)
    simpa [MvPolynomial.aeval_zero] using hcoeff
  have hzlocus : MvPolynomial.zeroLocus K I = ({(0 : ι → K)} : Set (ι → K)) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxzero : ¬ ∃ i : ι, x i ≠ 0 := by
        intro hxnonzero
        rcases hno x hxnonzero with ⟨k, hk⟩
        apply hk
        rw [MvPolynomial.zeroLocus_span] at hx
        exact hx (P k) ⟨k, rfl⟩
      simp only [Set.mem_singleton_iff]
      ext i
      by_contra hxi
      exact hxzero ⟨i, hxi⟩
    · intro x hx
      simpa [Set.mem_singleton_iff.mp hx] using hzero_mem
  have hrad :
      I.radical = MvPolynomial.idealOfVars ι K := by
    calc
      I.radical = MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
        rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
      _ = MvPolynomial.vanishingIdeal K ({(0 : ι → K)} : Set (ι → K)) := by
        rw [hzlocus]
      _ = MvPolynomial.idealOfVars ι K :=
        vanishingIdeal_singleton_zero_eq_idealOfVars
  have hheightI : I.height = Fintype.card ι := by
    calc
      I.height = I.radical.height := (ideal_height_radical I).symm
      _ = (MvPolynomial.idealOfVars ι K).height := by rw [hrad]
      _ = Fintype.card ι := hheight
  have hI_ne_top : I ≠ ⊤ := by
    intro htop
    have htopHeight : I.height = ⊤ := by
      simp [htop]
    have hcardTop : ((Fintype.card ι : ℕ∞) = ⊤) := by
      rw [← hheightI]
      exact htopHeight
    exact (ENat.natCast_ne_top (Fintype.card ι)) hcardTop
  have hheight_le : (Fintype.card ι : ℕ∞) ≤ (I.spanFinrank : ℕ∞) := by
    simpa [hheightI] using (Ideal.height_le_spanFinrank I hI_ne_top)
  have hspan_le_nat : I.spanFinrank ≤ Fintype.card κ := by
    calc
      I.spanFinrank ≤ (Set.range P).ncard := by
        simpa [I] using
          (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range P))
      _ ≤ Fintype.card κ := by
        rw [Set.ncard_eq_toFinset_card (Set.range P) (Set.finite_range P)]
        rw [Set.Finite.card_toFinset (Set.finite_range P)]
        exact Fintype.card_range_le P
  have hcard_le : Fintype.card ι ≤ Fintype.card κ :=
      ENat.natCast_le_natCast.mp (hheight_le.trans (ENat.natCast_le_natCast.mpr hspan_le_nat))
  exact (not_le_of_gt hcard) hcard_le

/--
Common-zero theorem for homogeneous equations over an algebraically closed
field.

If there are fewer homogeneous equations than variables and all equations have
positive degree, then the equations have a common nonzero zero.
-/
theorem algebraicallyClosed_commonZero_of_homogeneous
    (K : Type) [Field K] [IsAlgClosed K] :
    ProjectiveHomogeneousDimensionStatement K :=
  projectiveHomogeneousDimensionStatement_of_idealOfVarsHeightStatement
    (mvPolynomialIdealOfVarsHeightStatement_theorem K)

end MatrixSOS
