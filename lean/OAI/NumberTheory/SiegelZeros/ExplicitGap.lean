import OAI.NumberTheory.DirichletL.Nonvanishing

namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets

/-- An explicit uniform exclusion region for real zeros of Dirichlet
`L`-functions, derived directly from the `7 / 8` zero-free half-plane.

The constant `c = log 3 / 8 ≈ 0.137` is explicit. The existing formalization
(`OAI.SiegelZeros.WeightedTorusJets.dirichlet_real_zero_bound`) establishes
only the existence of *some* `c > 0`, via a non-constructive contradiction
through Bezout/intersection machinery; no value is given. Moreover, that
statement is restricted to primitive, real-valued, nonprincipal characters,
whereas the argument below applies to *every* Dirichlet character, including
the principal character: for a real zero `β ∈ (0, 1)` the pole-exclusion
hypothesis `¬ (χ = 1 ∧ (β : ℂ) = 1)` of the `7 / 8` theorem follows from
`β < 1` alone.

Since the `7 / 8` theorem excludes *all* zeros with `Re s > 7 / 8`, any real
zero `β ∈ (0, 1)` satisfies `β ≤ 7 / 8`, whence
`(1 - β) * log q ≥ (1 / 8) * log 3` for `q ≥ 3`. -/
theorem exists_explicit_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
      ∀ β : ℝ, 0 < β → β < 1 →
        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 / 8, by linarith, ?_⟩
  intro q _ hq3 χ β hβ0 hβ1 hzero
  -- Every real zero in `(0, 1)` lies at or below `7 / 8`, by the `7 / 8` bound.
  -- The pole case `χ = 1 ∧ (β : ℂ) = 1` is impossible since `β < 1`.
  have hβ78 : β ≤ 7 / 8 := by
    by_contra hlt
    push Not at hlt
    have hs : (7 / 8 : ℝ) < ((β : ℂ)).re := by simpa using hlt
    have hexc : ¬ (χ = 1 ∧ ((β : ℂ)) = 1) := by
      rintro ⟨-, hcon⟩
      have hβeq : β = 1 := by simpa using congrArg Complex.re hcon
      linarith
    exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      χ hs hexc hzero
  have hlog : Real.log 3 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
  have h1 : (1 : ℝ) / 8 ≤ 1 - β := by linarith
  calc Real.log 3 / 8 = (1 / 8) * Real.log 3 := by ring
    _ ≤ (1 - β) * Real.log 3 :=
        mul_le_mul_of_nonneg_right h1 hlog3.le
    _ ≤ (1 - β) * Real.log (q : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)

end WeightedTorusJets
end SiegelZeros
end OAI
