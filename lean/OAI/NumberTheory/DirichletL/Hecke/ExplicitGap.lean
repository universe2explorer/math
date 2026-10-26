import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing

namespace OAI
namespace SevenEighths
namespace HeckeFamily

/-- An explicit uniform exclusion region for real zeros of finite-order Hecke
`L`-functions over `ℚ(√-3)`, derived directly from the `7 / 8` zero-free
half-plane.

The constant `c = log 3 / 8 ≈ 0.137` is explicit, and the statement covers
every finite-order Hecke character (the repo's Siegel formalization treats
only Dirichlet `L`-functions). Here `χ.period` plays the role of the
conductor: for characters obtained via `Character.ofResidue` it is the
absolute norm `|O ⧸ 𝔪|` of the modulus ideal. The pole-exclusion hypothesis
`¬ (χ.residue = 1 ∧ (β : ℂ) = 1)` of the `7 / 8` theorem follows from
`β < 1` alone.

Since the `7 / 8` theorem excludes *all* zeros with `Re s > 7 / 8`, any real
zero `β ∈ (0, 1)` satisfies `β ≤ 7 / 8`, whence
`(1 - β) * log χ.period ≥ (1 / 8) * log 3` for `χ.period ≥ 3`.

DRAFT (2026-10-20): written, not yet compiled. The proof is the same skeleton
as `OAI.SiegelZeros.WeightedTorusJets.exists_explicit_real_zero_gap`, whose
tactic script was verified against Mathlib (axioms `propext`,
`Classical.choice`, `Quot.sound`). -/
theorem exists_explicit_hecke_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ χ : Character, 3 ≤ χ.period →
      ∀ β : ℝ, 0 < β → β < 1 →
        LFunction χ (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (χ.period : ℝ) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 / 8, by linarith, ?_⟩
  intro χ hper β hβ0 hβ1 hzero
  -- Every real zero in `(0, 1)` lies at or below `7 / 8`, by the `7 / 8` bound.
  -- The pole case `χ.residue = 1 ∧ (β : ℂ) = 1` is impossible since `β < 1`.
  have hβ78 : β ≤ 7 / 8 := by
    by_contra hlt
    push Not at hlt
    have hs : (7 / 8 : ℝ) < ((β : ℂ)).re := by simpa using hlt
    have hexc : ¬ (χ.residue = 1 ∧ ((β : ℂ)) = 1) := by
      rintro ⟨-, hcon⟩
      have hβeq : β = 1 := by simpa using congrArg Complex.re hcon
      linarith
    exact LFunction_ne_zero_of_seven_eighths_lt_re χ hs hexc hzero
  have hlog : Real.log 3 ≤ Real.log (χ.period : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hper)
  have h1 : (1 : ℝ) / 8 ≤ 1 - β := by linarith
  calc Real.log 3 / 8 = (1 / 8) * Real.log 3 := by ring
    _ ≤ (1 - β) * Real.log 3 :=
        mul_le_mul_of_nonneg_right h1 hlog3.le
    _ ≤ (1 - β) * Real.log (χ.period : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)

end HeckeFamily
end SevenEighths
end OAI
