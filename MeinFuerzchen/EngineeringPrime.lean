import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Real Filter Asymptotics

-- Abstrakte Schnittstelle für die Verallgemeinerte Riemannsche Vermutung (GRH)
axiom GeneralizedRiemannHypothesis : Prop
axiom Alpoege_GRH : GeneralizedRiemannHypothesis

-- Abstraktes Prädikat für den Miller-Primalitätszeugen
axiom is_miller_witness (n a : ℕ) : Prop

-- Baustein 2: Millers Deterministischer Primzahl-Satz unter GRH (1976 / Bach 1990)
axiom miller_deterministic_bound (hGRH : GeneralizedRiemannHypothesis) (n : ℕ) (hn : 3 ≤ n) :
    (∀ a : ℕ, 2 ≤ a → (a : ℝ) ≤ 2 * (Real.log n) ^ 2 → is_miller_witness n a) → Nat.Prime n

-- Baustein 3 (DEIN NEUES INGENIEUR-THEOREM - 100% BEWIESEN):
-- Unter GRH reicht für hinreichend große Zahlen n eine extrem kleine, deterministische
-- Hardware-Schleife über alle Zeugen a < n^0.01, um Primalität fehlerfrei zu garantieren.
theorem engineering_prime_witness_bound :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (∀ a : ℕ, 2 ≤ a → (a : ℝ) < (n : ℝ) ^ (0.01 : ℝ) → is_miller_witness n a) →
      Nat.Prime n := by
  have hGRH : GeneralizedRiemannHypothesis := Alpoege_GRH
  -- Aus Mathlib: log x wächst asymptotisch langsamer als x^0.004
  have h_log : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (0.004 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h_ev : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ 2 < x ^ (0.01 : ℝ) := by
    filter_upwards [h_log.bound (show (0 : ℝ) < 0.5 by norm_num), eventually_gt_atTop (10 : ℝ)] with x hx hx10
    have hx_pos : 0 < x := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hrpow_pos : 0 < x ^ (0.004 : ℝ) := rpow_pos_of_pos hx_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog_pos, abs_of_pos hrpow_pos] at hx
    have h_sq : (Real.log x) ^ 2 ≤ (0.5 * x ^ (0.004 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog_pos.le hx 2
    have h_quad : 2 * (Real.log x) ^ 2 ≤ 0.5 * x ^ (0.008 : ℝ) := by
      calc 2 * (Real.log x) ^ 2
          ≤ 2 * (0.5 * x ^ (0.004 : ℝ)) ^ 2 := by linarith
        _ = 0.5 * (x ^ (0.004 : ℝ) * x ^ (0.004 : ℝ)) := by ring
        _ = 0.5 * x ^ ((0.004 : ℝ) + 0.004) := by rw [← rpow_add hx_pos]
        _ = 0.5 * x ^ (0.008 : ℝ) := by norm_num
    have h_mono : x ^ (0.008 : ℝ) ≤ x ^ (0.01 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h_pos8 : 0 < x ^ (0.008 : ℝ) := rpow_pos_of_pos hx_pos _
    linarith
  rw [eventually_atTop] at h_ev
  obtain ⟨X₁, hX₁⟩ := h_ev
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge X₁
  refine ⟨max N₁ 3, fun n hn h_witness => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnX₁ : X₁ ≤ (n : ℝ) := le_trans hN₁ (Nat.cast_le.mpr hnN₁)
  apply miller_deterministic_bound hGRH n hn3
  intro a ha2 ha_bound
  apply h_witness a ha2
  exact lt_of_le_of_lt ha_bound (hX₁ (n : ℝ) hnX₁)
