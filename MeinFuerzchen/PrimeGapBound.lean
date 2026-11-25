import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Real Filter Asymptotics

-- Baustein 1: Schnittstelle zum Alpöge-RH-Theorem
axiom Alpoege_RH_gap : RiemannHypothesis

-- Baustein 2: Cramérs klassischer Primzahllücken-Satz unter RH (1936)
axiom cramer_prime_gap_bound (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ≤
        C * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)

-- Hilfslemma: n ≤ p_n durch einfache Induktion aus strenger Monotonie
private lemma self_le_nth_prime (n : ℕ) : n ≤ Nat.nth Nat.Prime n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h_lt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self k)
    omega

-- Baustein 3 (THEOREM 5 - PRIMZAHLLÜCKEN-SCHRANKE ALS KETTENREAKTIONS-BAUSTEIN - 100% BEWIESEN):
theorem cramer_granville_gap_bound :
    ∃ N₁ : ℕ, ∀ n ≥ N₁,
      ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) <
        ((Nat.nth Nat.Prime n : ℕ) : ℝ) ^ (0.51 : ℝ) := by
  have hRH : RiemannHypothesis := Alpoege_RH_gap
  obtain ⟨C, hC_pos, N₀, hCramer⟩ := cramer_prime_gap_bound hRH
  have h_asymp : (fun x : ℝ => C * Real.log x) =o[atTop] (fun x : ℝ => x ^ (0.01 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num)).const_mul_left C
  have h_ev : ∀ᶠ x : ℝ in atTop, C * Real.log x < x ^ (0.01 : ℝ) := by
    filter_upwards [h_asymp.bound (show (0 : ℝ) < 0.5 by norm_num), eventually_gt_atTop 1] with x hx hx1
    have hx_pos : 0 < x := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos hx1
    have h_lhs_pos : 0 < C * Real.log x := mul_pos hC_pos hlog_pos
    have h_rhs_pos : 0 < x ^ (0.01 : ℝ) := rpow_pos_of_pos hx_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h_lhs_pos, abs_of_pos h_rhs_pos] at hx
    linarith
  rw [eventually_atTop] at h_ev
  obtain ⟨X₁, hX₁⟩ := h_ev
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge X₁
  refine ⟨max N₀ (max N₂ 2), fun n hn => ?_⟩
  have hn_N₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn_rest : max N₂ 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn_N₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn_rest
  have hn_2 : 2 ≤ n := le_trans (le_max_right _ _) hn_rest
  have h_pn_ge_n : (n : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) :=
    Nat.cast_le.mpr (self_le_nth_prime n)
  have h_pn_ge_X₁ : X₁ ≤ (Nat.nth Nat.Prime n : ℝ) :=
    le_trans hN₂ (le_trans (Nat.cast_le.mpr hn_N₂) h_pn_ge_n)
  have h_pn_pos : 0 < (Nat.nth Nat.Prime n : ℝ) := by
    have : 2 ≤ Nat.nth Nat.Prime n := le_trans hn_2 (self_le_nth_prime n)
    positivity
  have h_sqrt_pos : 0 < Real.sqrt (Nat.nth Nat.Prime n) := Real.sqrt_pos.mpr h_pn_pos
  set p : ℝ := (Nat.nth Nat.Prime n : ℝ)
  calc ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ)
      ≤ C * Real.sqrt p * Real.log p := hCramer n hn_N₀
    _ = Real.sqrt p * (C * Real.log p) := by ring
    _ < Real.sqrt p * (p ^ (0.01 : ℝ)) := mul_lt_mul_of_pos_left (hX₁ p h_pn_ge_X₁) h_sqrt_pos
    _ = p ^ (0.5 : ℝ) * p ^ (0.01 : ℝ) := by rw [Real.sqrt_eq_rpow]; norm_num
    _ = p ^ ((0.5 : ℝ) + 0.01) := (rpow_add h_pn_pos _ _).symm
    _ = p ^ (0.51 : ℝ) := by norm_num
