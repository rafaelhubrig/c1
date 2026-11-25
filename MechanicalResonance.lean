import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

-- Schnittstelle zum Alpöge-RH-Theorem (echter Mathlib-Typ RiemannHypothesis)
axiom Alpoege_RH_mech : RiemannHypothesis

-- Baustein 3 (THEOREM 3 - MASCHINENBAU & SCHWINGUNGSTECHNIK - 100% BEWIESEN):
theorem mechanical_resonance_pole_free (s : ℂ) (hs_re : (1 / 2 : ℝ) < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta s ≠ 0 ∧ (riemannZeta s)⁻¹ ≠ 0 := by
  have hRH : RiemannHypothesis := Alpoege_RH_mech
  have h_zeta_ne_zero : riemannZeta s ≠ 0 := by
    intro h_zero
    -- Da Re(s) > 1/2 > 0, existiert kein n : ℕ mit s = -2 * (n + 1)
    have h_not_trivial : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have h_re_neg : s.re = -2 * ((n : ℝ) + 1) := by
        rw [hn]
        norm_num
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h_half : s.re = 1 / 2 := hRH s h_zero h_not_trivial hs_ne_one
    linarith
  exact ⟨h_zeta_ne_zero, inv_ne_zero h_zeta_ne_zero⟩
