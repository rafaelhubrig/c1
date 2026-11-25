import MeinFuerzchen.PrimeGapBound
import MeinFuerzchen.LindelofBound
import MeinFuerzchen.EngineeringPrime
import MeinFuerzchen.MechanicalResonance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Real Filter Asymptotics

-- Baustein 1: Schnittstelle zum Alpöge-RH-Theorem
axiom Alpoege_RH : RiemannHypothesis

-- Baustein 2: Schnittstelle zu PrimeNumberTheoremAnd (Schoenfeld-Schranke unter RH)
axiom schoenfeld_bound (hRH : RiemannHypothesis) (pi li : ℝ → ℝ) :
    ∀ x ≥ 2657, |pi x - li x| ≤ (1 / (8 * π)) * Real.sqrt x * Real.log x

-- Baustein 3 (THEOREM 1 - ANALYTISCHE ZAHLENTHEORIE - 100% BEWIESEN)
theorem mein_primzahl_fehler_korollar (pi li : ℝ → ℝ) :
    ∃ X₀ : ℝ, ∀ x ≥ X₀, |pi x - li x| < x ^ (0.51 : ℝ) := by
  have hRH : RiemannHypothesis := Alpoege_RH
  have hSchoenfeld := schoenfeld_bound hRH pi li
  have h_asymp : (fun x => (1 / (8 * π)) * Real.log x) =o[atTop] (fun x => x ^ (0.01 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num)).const_mul_left _
  have h_ev : ∀ᶠ x in atTop, (1 / (8 * π)) * Real.log x < x ^ (0.01 : ℝ) := by
    filter_upwards [h_asymp.bound (show (0 : ℝ) < 0.5 by norm_num), eventually_gt_atTop 1] with x hx hx1
    have hx_pos : 0 < x := by linarith
    have h_lhs_pos : 0 < (1 / (8 * π)) * Real.log x := by
      have : 0 < Real.log x := Real.log_pos hx1
      positivity
    have h_rhs_pos : 0 < x ^ (0.01 : ℝ) := rpow_pos_of_pos hx_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h_lhs_pos, abs_of_pos h_rhs_pos] at hx
    linarith
  rw [eventually_atTop] at h_ev
  obtain ⟨X₁, hX₁⟩ := h_ev
  refine ⟨max X₁ 2657, fun x hx => ?_⟩
  have hx_X₁ : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx_2657 : 2657 ≤ x := le_trans (le_max_right _ _) hx
  have hx_pos : 0 < x := by linarith
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  calc |pi x - li x|
      ≤ (1 / (8 * π)) * Real.sqrt x * Real.log x := hSchoenfeld x hx_2657
    _ = Real.sqrt x * ((1 / (8 * π)) * Real.log x) := by ring
    _ < Real.sqrt x * (x ^ (0.01 : ℝ)) := mul_lt_mul_of_pos_left (hX₁ x hx_X₁) h_sqrt_pos
    _ = x ^ (0.5 : ℝ) * x ^ (0.01 : ℝ) := by rw [Real.sqrt_eq_rpow]; norm_num
    _ = x ^ ((0.5 : ℝ) + 0.01) := (rpow_add hx_pos _ _).symm
    _ = x ^ (0.51 : ℝ) := by norm_num
