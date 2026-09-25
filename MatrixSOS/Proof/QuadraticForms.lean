/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic forms associated with polynomial matrices
-/

noncomputable section

namespace MatrixSOS

theorem exists_first_nonzero_of_ternary_isotropic
    {K : Type*}
    [Field K]
    [CharZero K]
    {a b x₀ y₀ z₀ : K}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (hneq : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0)
    (hxyz : x₀ ^ 2 = a * y₀ ^ 2 + b * z₀ ^ 2) :
    ∃ x y z : K, x ≠ 0 ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2 := by
  by_cases hx0 : x₀ = 0
  · have hsum : a * y₀ ^ 2 + b * z₀ ^ 2 = 0 := by
      simpa [hx0] using hxyz.symm
    have hy0 : y₀ ≠ 0 := by
      intro hy0
      have hbz : b * z₀ ^ 2 = 0 := by simpa [hy0] using hsum
      have hzsq : z₀ ^ 2 = 0 := (mul_eq_zero.mp hbz).resolve_left hb0
      have hz0 : z₀ = 0 := sq_eq_zero_iff.mp hzsq
      rcases hneq with hx | hy | hz
      · exact (hx hx0).elim
      · exact (hy hy0).elim
      · exact (hz hz0).elim
    have hz0 : z₀ ≠ 0 := by
      intro hz0
      have hay : a * y₀ ^ 2 = 0 := by simpa [hz0] using hsum
      have hysq : y₀ ^ 2 = 0 := (mul_eq_zero.mp hay).resolve_left ha0
      have hy0' : y₀ = 0 := sq_eq_zero_iff.mp hysq
      rcases hneq with hx | hy | hz
      · exact (hx hx0).elim
      · exact (hy hy0').elim
      · exact (hz hz0).elim
    refine ⟨2 * a * y₀, (a + 1) * y₀, (1 - a) * z₀, ?_, ?_⟩
    · simpa [mul_assoc] using
        mul_ne_zero (mul_ne_zero (show (2 : K) ≠ 0 by norm_num) ha0) hy0
    · have hcalc :
          a * ((a + 1) * y₀) ^ 2 + b * ((1 - a) * z₀) ^ 2 =
            (2 * a * y₀) ^ 2 + (1 - a) ^ 2 * (a * y₀ ^ 2 + b * z₀ ^ 2) := by
          ring
      calc
        (2 * a * y₀) ^ 2
            = (2 * a * y₀) ^ 2 + (1 - a) ^ 2 * (a * y₀ ^ 2 + b * z₀ ^ 2) := by
                simp [hsum]
        _ = a * ((a + 1) * y₀) ^ 2 + b * ((1 - a) * z₀) ^ 2 := by
              rw [hcalc]
  · exact ⟨x₀, y₀, z₀, hx0, hxyz⟩

theorem exists_pfister2_isotropic_of_exists_ternary_isotropic
    {K : Type*}
    [Field K]
    {a b : K}
    (h : ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2) :
    ∃ x y z w : K,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * w ^ 2 = 0 := by
  rcases h with ⟨x, y, z, hneq, hxyz⟩
  refine ⟨x, y, z, 0, ?_, ?_⟩
  · rcases hneq with hx | hy | hz
    · exact Or.inl hx
    · exact Or.inr <| Or.inl hy
    · exact Or.inr <| Or.inr <| Or.inl hz
  · calc
      x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * (0 : K) ^ 2
          = x ^ 2 - (a * y ^ 2 + b * z ^ 2) := by ring
      _ = 0 := by rw [hxyz]; ring

/-- Explicit descent from isotropy of the associated 2-fold Pfister form
`⟨1, -a, -b, ab⟩` to isotropy of the ternary subform `⟨1, -a, -b⟩`. -/
theorem exists_ternary_isotropic_of_exists_pfister2_isotropic
    {K : Type*}
    [Field K]
    {a b : K}
    (h : ∃ x y z w : K,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * w ^ 2 = 0) :
    ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2 := by
  rcases h with ⟨x, y, z, w, hneq, hpf⟩
  by_cases hΔ : z ^ 2 - a * w ^ 2 = 0
  · by_cases hzw : z = 0 ∧ w = 0
    · have hxy0 : x ≠ 0 ∨ y ≠ 0 := by
        rcases hneq with hx | hy | hz | hw
        · exact Or.inl hx
        · exact Or.inr hy
        · exact False.elim (hz hzw.1)
        · exact False.elim (hw hzw.2)
      refine ⟨x, y, 0, ?_, ?_⟩
      · rcases hxy0 with hx | hy
        · exact Or.inl hx
        · exact Or.inr <| Or.inl hy
      · have hxy : x ^ 2 - a * y ^ 2 = 0 := by
          simpa [hzw.1, hzw.2] using hpf
        have hxy' : x ^ 2 = a * y ^ 2 := sub_eq_zero.mp hxy
        simp [hxy']
    · have hzw' : z ≠ 0 ∨ w ≠ 0 := by
        by_contra hzw'
        apply hzw
        push Not at hzw'
        exact ⟨hzw'.1, hzw'.2⟩
      refine ⟨z, w, 0, ?_, ?_⟩
      · rcases hzw' with hz | hw
        · exact Or.inl hz
        · exact Or.inr <| Or.inl hw
      · have hzwEq : z ^ 2 = a * w ^ 2 := sub_eq_zero.mp hΔ
        simp [hzwEq]
  · let Δ : K := z ^ 2 - a * w ^ 2
    let X : K := x * z + a * y * w
    let Y : K := x * w + y * z
    let Z : K := Δ
    refine ⟨X, Y, Z, ?_, ?_⟩
    · exact Or.inr <| Or.inr <| by
        simpa [Z, Δ] using hΔ
    · have hxy : x ^ 2 - a * y ^ 2 = b * Δ := by
        dsimp [Δ]
        calc
          x ^ 2 - a * y ^ 2 = b * z ^ 2 - a * b * w ^ 2 := by
              apply sub_eq_zero.mp
              calc
                (x ^ 2 - a * y ^ 2) - (b * z ^ 2 - a * b * w ^ 2)
                    = x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * w ^ 2 := by ring
                _ = 0 := hpf
          _ = b * (z ^ 2 - a * w ^ 2) := by ring
      have hmain : X ^ 2 - a * Y ^ 2 = b * Z ^ 2 := by
        dsimp [X, Y, Z, Δ]
        calc
          (x * z + a * y * w) ^ 2 - a * (x * w + y * z) ^ 2
              = (x ^ 2 - a * y ^ 2) * (z ^ 2 - a * w ^ 2) := by ring
          _ = (b * (z ^ 2 - a * w ^ 2)) * (z ^ 2 - a * w ^ 2) := by rw [hxy]
          _ = b * (z ^ 2 - a * w ^ 2) ^ 2 := by ring
      calc
        X ^ 2 = a * Y ^ 2 + (X ^ 2 - a * Y ^ 2) := by ring
        _ = a * Y ^ 2 + b * Z ^ 2 := by rw [hmain]

end MatrixSOS
