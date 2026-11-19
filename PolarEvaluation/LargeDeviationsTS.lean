import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments
import PolarEvaluation.LargeDeviationsT

/-!
# Large-Deviation Bounds for `S(t, χ)` in the t-Aspect (Corollary 1.6(i))
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Classical

namespace PolarEvaluation

/-- **Corollary 1.6(i)** (`t`-aspect large-deviation bound for `|S(t, χ)|`). -/
theorem S_large_deviation_t (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ) :
    ∀ α > 0, ∃ (c T₀ : ℝ), c > 0 ∧ T₀ ≥ 100 ∧
      ∀ T ≥ T₀,
        let V := α * Real.sqrt (Real.log T * Real.log (Real.log T))
        V ≤ Real.log T / Real.log (Real.log T) →
        (volume { t ∈ Set.Icc T (2 * T) |
          D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
          T * Real.exp (-c * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ)) := by
  intro α hα
  obtain ⟨C₀, hC₀, h_hzs_S⟩ := S_val_horizontal_zero_sum D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C₃, hΔ₀, hC₃, h_ccm⟩ := ccm_odd_extremal
  let C_L1_tot : ℝ := max (C₃ * Real.pi) (Real.pi / 2 + C₃ + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_t_aspect (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  let K_scale : ℝ := 2
  let C_B : ℝ := 32 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8)))
  let L_α : ℝ := max 100 (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))
  let T₀ : ℝ := max (max 100 ((q : ℝ) * 4 + 4)) (Real.exp (Real.exp L_α))
  let c : ℝ := 1 / (32 * (2 * Real.pi * K_scale))
  refine ⟨c, T₀, by positivity, le_trans (le_max_left _ _) (le_max_left _ _), fun T hT V hV_ub => ?_⟩
  have hT_ge_100 : 100 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_pos : 0 < T := by linarith
  have hT_ge_exp : Real.exp (Real.exp L_α) ≤ T := le_trans (le_max_right _ _) hT
  have hlogT_ge_exp : Real.exp L_α ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hT_ge_exp
  have hLLT_ge : L_α ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogT_ge_exp
  have hLLT_pos : 0 < Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
  have hlogT_pos : 0 < Real.log T := by linarith [Real.exp_pos L_α]
  have hq_2T : (q : ℝ) * (2 * T + 2) ≤ T ^ 2 := by
    have hq4 : (q : ℝ) * 4 + 4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    nlinarith
  have hlog_q2T_le : Real.log ((q : ℝ) * (2 * T + 2)) ≤ 2 * Real.log T := by
    have h1 : Real.log ((q : ℝ) * (2 * T + 2)) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) hq_2T
    rwa [Real.log_pow] at h1
  have hlog_q2T_ge : Real.log T ≤ Real.log ((q : ℝ) * (2 * T + 2)) := by
    refine Real.log_le_log hT_pos ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have h_ratio_ge : (Real.log T / Real.log (Real.log T)) ≥ (Real.log (Real.log T)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log T)) hLLT_pos.le 4
    have h3 : (Real.log (Real.log T)) ^ 4 / 24 ≤ Real.log T := by
      calc (Real.log (Real.log T)) ^ 4 / 24 = (Real.log (Real.log T)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log T)) := he4
        _ = Real.log T := Real.exp_log hlogT_pos
    have h_llt : 24 ≤ Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
    rw [ge_iff_le, le_div_iff₀ hLLT_pos]; nlinarith [pow_nonneg hLLT_pos.le 3]
  have hV_lb : A * Real.log (Real.log T) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log T) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge)))
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log T)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log T)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log T) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      rw [← Real.sqrt_sq hLLT_pos.le]; exact Real.sqrt_le_sqrt h_ratio_ge
    have h4 : A / α ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have : 1 ≤ Real.log (Real.log T) := by linarith
      calc A / α ≤ Real.sqrt (Real.log (Real.log T)) := h2
        _ ≤ Real.log (Real.log T) := by rw [← Real.sqrt_sq hLLT_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := h3
    have h5 : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]; field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    rw [← div_le_iff₀ hLLT_pos, h5, ← div_le_iff₀' hα]; exact h4
  have hV_pos : 0 < V := by
    have : 0 < A := by linarith [le_max_left (2 : ℝ) (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8)))]
    nlinarith
  let Δ : ℝ := K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log T) ≤ Δ := by
      dsimp only [Δ]; rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log T) ≤ Real.log T := by rwa [le_div_iff₀ hLLT_pos] at hV_ub
      calc K_scale * Real.log (Real.log T) * V = K_scale * (V * Real.log (Real.log T)) := by ring
        _ ≤ K_scale * Real.log T := by gcongr
        _ ≤ K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log T) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log T) :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLT_ge)
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log T / 2 := by
    rw [hlogX_eq]
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log T) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge))
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log T) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log T := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log T := by gcongr; rw [div_le_iff₀ hV_pos]; linarith
      _ = Real.log T / 2 := by ring
  have hX_le_T : X ≤ T := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hT_pos, Real.log_exp]; linarith [hlogX_le_half, hlogX_eq]
  have hlogX_pos : 0 < Real.log X := by rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor (Real.log T / Real.log X)
  have hk_ge_2 : 2 ≤ k := by
    have h1 : 2 ≤ Real.log T / Real.log X := by rw [le_div_iff₀ hlogX_pos]; linarith
    exact Nat.le_floor h1
  have hXk_le_T : X ^ k ≤ T := by
    rw [← Real.log_le_log_iff (pow_pos (Real.exp_pos _) _) hT_pos, Real.log_pow]
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    rw [le_div_iff₀ hlogX_pos] at hk_le; exact hk_le
  have hk_lb : V / (2 * (2 * Real.pi * K_scale)) ≤ k := by
    have h_le : Real.log T / Real.log X < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h_k2 : Real.log T / Real.log X / 2 ≤ (k : ℝ) := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge_2
      linarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log T / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log T) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log T / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log T / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    have h_lx : 2 * Real.pi * K_scale * Real.log T / V ≤ Real.log X := by
      rw [hlogX_eq]; dsimp only [Δ]
      calc 2 * Real.pi * K_scale * Real.log T / V ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by ring
    calc (k : ℝ) ≤ Real.log T / Real.log X := hk_le
      _ ≤ Real.log T / (2 * Real.pi * K_scale * Real.log T / V) := div_le_div_of_nonneg_left hlogT_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by field_simp [hlogT_pos.ne', Real.pi_ne_zero]; ring
  obtain ⟨M_plus, M_minus, hMp_exp, hMm_exp, hM_im, hM_maj, hM_sup, hMp_int, hMm_int⟩ := h_ccm Δ hΔ_ge_Δ₀
  have hMp_real : Integrable (fun x : ℝ => (M_plus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_plus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMp_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).1
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hMm_real : Integrable (fun x : ℝ => (M_minus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_minus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMm_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).2
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hK_pi2_zero : ∫ x : ℝ, kernelK (Real.pi / 2) x = 0 := by
    rw [kernelK_integral_eq (Real.pi / 2), Real.cos_pi_div_two, mul_zero]
  have h_exp_le : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
    have he := Real.add_one_le_exp (2 * Real.pi * Δ)
    have h3 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [Real.two_le_pi]
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3.trans_eq (one_mul _).symm
  have h_exp_1Δ : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
  have hMp_int_re : Integrable (fun x : ℝ => (M_plus x).re) :=
    hMp_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMm_int_re : Integrable (fun x : ℝ => (M_minus x).re) :=
    hMm_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMp_L1_diff : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, ((M_plus x).re - kernelK (Real.pi / 2) x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).2)
    rw [h_eq, integral_sub hMp_int_re (kernelK_integrable (Real.pi / 2)), hK_pi2_zero, sub_zero]
    have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMp_int).2]
    calc ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMp_L1 : ∫ x : ℝ, |(M_plus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_plus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMp_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).1.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  have hMm_L1_diff : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, (kernelK (Real.pi / 2) x - (M_minus x).re) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).1)
    rw [h_eq, integral_sub (kernelK_integrable (Real.pi / 2)) hMm_int_re, hK_pi2_zero, zero_sub]
    have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMm_int).1]
    calc -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMm_L1 : ∫ x : ℝ, |(M_minus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_minus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMm_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).2.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  let h_hat_p := fourierHat (fun x : ℝ => ((M_plus x).re : ℂ))
  let h_hat_m := fourierHat (fun x : ℝ => ((M_minus x).re : ℂ))
  have h_tail_p := h_tail q χ Δ (fun x => (M_plus x).re) hΔ_ge_Δ₀ hMp_real hMp_L1_diff hMp_L1
  have h_tail_m := h_tail q χ Δ (fun x => (M_minus x).re) hΔ_ge_Δ₀ hMm_real hMm_L1_diff hMm_L1
  let S_p : Set ℝ := { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat_p X t| ≥ V / 4 }
  let S_m : Set ℝ := { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat_m X t| ≥ V / 4 }
  have h_subset : { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V } ⊆ S_p ∪ S_m := by
    intro t ⟨ht_icc, ht_nv, ht_S⟩
    have hq1_t : q = 1 → |t| ≥ 10 := fun _ => by rw [abs_of_pos (by linarith [ht_icc.1])]; linarith [ht_icc.1]
    obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs_S q hq χ hχ hGRH t ht_nv hq1_t
    set Q : ℝ := analyticConductor q t
    have hQ_le : Q ≤ (q : ℝ) * (2 * T + 2) := by
      dsimp only [Q, analyticConductor]
      have ht_abs : |t| ≤ 2 * T := by rw [abs_of_pos (by linarith [ht_icc.1])]; exact ht_icc.2
      gcongr
    have hQ_ge_100 : 100 ≤ Q := by
      dsimp only [Q, analyticConductor]
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have ht1 : 100 ≤ |t| := by rw [abs_of_pos (by linarith [ht_icc.1])]; exact ht_icc.1
      nlinarith
    have h_exp_err : (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) ≤ C₃ * Real.log (Real.log T) := by
      have h_2piΔ : Real.log (Real.log T) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi]
        have h_v : V * Real.log (Real.log T) ≤ Real.log T := by rwa [le_div_iff₀ hLLT_pos] at hV_ub
        calc Real.log (Real.log T) ≤ Real.pi * K_scale * Real.log (Real.log T) := le_mul_of_one_le_left hLLT_pos.le h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log T) * V = Real.pi * K_scale * (V * Real.log (Real.log T)) := by ring
                _ ≤ Real.pi * K_scale * Real.log T := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by nlinarith [hlog_q2T_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log T := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogT_pos (by
          calc Real.log T = Real.exp (Real.log (Real.log T)) := (Real.exp_log hlogT_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      have h_logQ_le : Real.log Q ≤ 2 * Real.log T := (Real.log_le_log (by linarith) hQ_le).trans hlog_q2T_le
      calc (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ))
          ≤ (2 * Real.log T / (2 * Real.pi)) * (C₃ * (1 / Real.log T)) := by gcongr
        _ = C₃ / Real.pi := by field_simp [hlogT_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ C₃ * Real.log (Real.log T) := by
            have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
            nlinarith [hC₃]
    have h_gw_err : C₁ * (C₃ + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * C₃ else 0)) ≤
        2 * C₁ * C₃ * Real.log (Real.log T) := by
      have h_if : (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * C₃ else 0) ≤ C₃ := by
        split_ifs
        · have h_e : Real.exp (Real.pi * Δ) ≤ T := by
            have : Real.pi * Δ ≤ 2 * Real.pi * Δ := by nlinarith [Real.pi_pos]
            exact (Real.exp_le_exp.mpr this).trans hX_le_T
          have h_t2 : T ≤ t ^ 2 := by have : T ≤ t := ht_icc.1; nlinarith
          have h_div : Real.exp (Real.pi * Δ) / t ^ 2 ≤ 1 := div_le_one_of_le₀ (h_e.trans h_t2) (sq_nonneg t)
          exact mul_le_of_le_one_left hC₃.le h_div
        · exact hC₃.le
      have h1 : 1 ≤ Real.log (Real.log T) := by linarith
      nlinarith
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log T) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log T) + C₀ + 2 * C₁ * C₃ * Real.log (Real.log T) +
        C₃ * Real.log (Real.log T) ≤ Real.pi * V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have h_pi2 : 2 ≤ Real.pi := Real.two_le_pi
      nlinarith
    have h_pi_env : (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) ≤ Real.pi * V / 2 := by
      have h_logQ : Real.log Q ≤ Real.log ((q : ℝ) * (2 * T + 2)) := Real.log_le_log (by linarith) hQ_le
      calc (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ))
          = Real.log Q / (4 * Δ) := by field_simp [Real.pi_ne_zero]; ring
        _ ≤ Real.log ((q : ℝ) * (2 * T + 2)) / (4 * Δ) := by gcongr
        _ = V / (4 * K_scale) := by dsimp only [Δ]; field_simp [hV_pos.ne']; ring
        _ = V / 8 := by dsimp only [K_scale]; ring
        _ ≤ Real.pi * V / 2 := by nlinarith [Real.two_le_pi, hV_pos]
    rcases le_abs.mp ht_S with hS_pos | hS_neg
    · left
      refine ⟨ht_icc, ?_⟩
      obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_plus Δ C₃ hΔ_ge_1 hC₃.le hMp_exp (fun x => (hM_sup x).1)
        (fun x => (hM_im x).1) t hq1_t
      have h_sum_le : ∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n) ≤
          ∑' n : ℕ, (M_plus (t - D.zeros q χ n)).re := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
        exact (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht_nv n))).2
      have h_hat_eq : fourierHat (fun x : ℝ => M_plus x) = h_hat_p := by
        ext ξ; unfold fourierHat; congr 1; ext x
        rw [Complex.ext ((rfl : (M_plus x).re = _)) (hM_im x).1]
      rw [h_hat_eq] at h_gw_bd
      have h_tail_t := h_tail_p t
      have h_p23 : |primeSum2 q χ h_hat_p X t + primeSumGe3 q χ h_hat_p X t| ≤ 2 * C_tail * Real.log (Real.log T) := by
        have h1 : |primeSum2 q χ h_hat_p X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_p X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_p X t) (primeSumGe3 q χ h_hat_p X t)]
      have h_P_split : primePowerSum q χ h_hat_p X t =
          primeSum1 q χ h_hat_p X t + primeSum2 q χ h_hat_p X t + primeSumGe3 q χ h_hat_p X t := by
        unfold primeSumGe3; ring
      have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_plus x).re) ≤
          Real.pi * V / 2 + C₃ * Real.log (Real.log T) := by
        have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMp_int).2]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        calc (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_plus x).re)
            ≤ (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
          _ = (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) + (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) := by ring
          _ ≤ Real.pi * V / 2 + C₃ * Real.log (Real.log T) := add_le_add h_pi_env h_exp_err
      have h_piV : Real.pi * V ≤ Real.pi * D.S_val q χ t := by gcongr
      have h_neg : -primeSum1 q χ h_hat_p X t ≥ Real.pi * V / 4 := by
        have h_g := (abs_le.mp h_gw_bd).2
        have h_h := (abs_le.mp h_hzs_bd).2
        have h_p := (abs_le.mp h_p23).1
        linarith
      have h_div_pi : V / 4 ≤ Real.pi * V / 4 := by nlinarith [Real.two_le_pi, hV_pos]
      exact le_trans h_div_pi (le_trans h_neg (neg_le_abs _))
    · right
      refine ⟨ht_icc, ?_⟩
      let M_neg : ℂ → ℂ := fun z => -M_minus z
      have hM_neg_exp : HasExponentialType M_neg (2 * Real.pi * Δ) := by
        refine ⟨hMm_exp.1.neg, fun ε hε => ?_⟩
        obtain ⟨C, hC, hbd⟩ := hMm_exp.2 ε hε
        exact ⟨C, hC, fun z => by simpa [M_neg, norm_neg] using hbd z⟩
      obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_neg Δ C₃ hΔ_ge_1 hC₃.le hM_neg_exp
        (fun x => by simpa [M_neg, norm_neg] using (hM_sup x).2)
        (fun x => by simp [M_neg, (hM_im x).2]) t hq1_t
      have h_sum_le : ∑' n : ℕ, (-kernelK (Real.pi / 2) (t - D.zeros q χ n)) ≤
          ∑' n : ℕ, (M_neg (t - D.zeros q χ n)).re := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K.neg hsumm_M
        simp only [M_neg, Complex.neg_re, neg_le_neg_iff]
        exact (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht_nv n))).1
      have h_hat_eq : fourierHat (fun x : ℝ => M_neg x) = fun ξ => -h_hat_m ξ := by
        ext ξ; unfold fourierHat h_hat_m; dsimp only [M_neg]
        have heq : (fun x : ℝ => -M_minus x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) =
            fun x : ℝ => -(((M_minus x).re : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
          ext x
          have hre : M_minus x = ((M_minus x).re : ℂ) := Complex.ext rfl (hM_im x).2
          rw [hre]; ring
        rw [heq, integral_neg]
      have h_pps_neg : primePowerSum q χ (fourierHat (fun x : ℝ => M_neg x)) X t = -primePowerSum q χ h_hat_m X t := by
        rw [h_hat_eq]
        unfold primePowerSum
        simp only [mul_neg, neg_add, ← neg_add_rev]
        rw [← Finset.sum_neg_distrib]
        congr 1; ext n
        · simp [Complex.neg_re]; ring
      rw [h_pps_neg] at h_gw_bd
      have h_tail_t := h_tail_m t
      have h_p23 : |primeSum2 q χ h_hat_m X t + primeSumGe3 q χ h_hat_m X t| ≤ 2 * C_tail * Real.log (Real.log T) := by
        have h1 : |primeSum2 q χ h_hat_m X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_m X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_m X t) (primeSumGe3 q χ h_hat_m X t)]
      have h_P_split : primePowerSum q χ h_hat_m X t =
          primeSum1 q χ h_hat_m X t + primeSum2 q χ h_hat_m X t + primeSumGe3 q χ h_hat_m X t := by
        unfold primeSumGe3; ring
      have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_neg x).re) ≤
          Real.pi * V / 2 + C₃ * Real.log (Real.log T) := by
        have h_int_eq : (∫ x : ℝ, (M_neg x).re) = -∫ x : ℝ, (M_minus x).re := by
          simp only [M_neg, Complex.neg_re, integral_neg]
        rw [h_int_eq]
        have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMm_int).1]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        calc (Real.log Q / (2 * Real.pi)) * (-∫ x : ℝ, (M_minus x).re)
            ≤ (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
          _ = (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) + (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) := by ring
          _ ≤ Real.pi * V / 2 + C₃ * Real.log (Real.log T) := add_le_add h_pi_env h_exp_err
      have h_piV : Real.pi * V ≤ -Real.pi * D.S_val q χ t := by nlinarith [Real.two_le_pi]
      have h_tsum_neg : ∑' n : ℕ, (-kernelK (Real.pi / 2) (t - D.zeros q χ n)) =
          -∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n) := tsum_neg
      have h_pos : primeSum1 q χ h_hat_m X t ≥ Real.pi * V / 4 := by
        have h_g := (abs_le.mp h_gw_bd).2
        have h_h := (abs_le.mp h_hzs_bd).1
        have h_p := (abs_le.mp h_p23).2
        linarith
      have h_div_pi : V / 4 ≤ Real.pi * V / 4 := by nlinarith [Real.two_le_pi, hV_pos]
      exact le_trans h_div_pi (le_trans h_pos (le_abs_self _))
  have h_meas_le : (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
      (volume S_p).toReal + (volume S_m).toReal := by
    have h_u := measure_mono h_subset |>.trans (measure_union_le S_p S_m)
    have h_fin_p : volume S_p ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top _ _).ne (measure_mono (fun _ h => h.1))
    have h_fin_m : volume S_m ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top _ _).ne (measure_mono (fun _ h => h.1))
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h_fin_p, h_fin_m⟩) h_u).trans_eq
      (ENNReal.toReal_add h_fin_p h_fin_m)
  have h_markov_branch : ∀ (h_hat : ℝ → ℂ) (M : ℝ → ℝ),
      Integrable (fun x : ℝ => M x - kernelK (Real.pi / 2) x) →
      (∫ x : ℝ, |M x - kernelK (Real.pi / 2) x|) ≤ C_L1_tot / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1_tot →
      h_hat = fourierHat (fun x : ℝ => (M x : ℂ)) →
      (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal ≤
        (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by
    intro h_hat M hM_diff hM_L1d hM_L1t hhat_eq
    subst hhat_eq
    let F_t : ℝ → ℝ := fun t => |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ^ (2 * k)
    have hF_cont : Continuous F_t := by
      dsimp only [F_t]; unfold primeSum1
      refine (Continuous.abs (continuous_const.mul (continuous_finset_sum _ fun p _ =>
        continuous_const.mul (Complex.continuous_re.comp ?_)))).pow (2 * k)
      refine Continuous.add ?_ ?_
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    have hF_int : IntegrableOn F_t (Set.Icc T (2 * T)) := hF_cont.continuousOn.integrableOn_Icc
    have h_markov : (V / 4) ^ (2 * k) *
        (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal ≤
        ∫ t in Set.Icc T (2 * T), F_t t := by
      have h_sub_set : { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 } =
          Set.Icc T (2 * T) ∩ { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t } := by
        ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ge_iff_le]
        constructor
        · rintro ⟨ht, h1⟩; exact ⟨ht, pow_le_pow_left₀ (by positivity) h1 (2 * k)⟩
        · rintro ⟨ht, h1⟩; refine ⟨ht, ?_⟩; by_contra hlt; push_neg at hlt
          have := pow_lt_pow_left₀ hlt (abs_nonneg _) (by positivity : 2 * k ≠ 0); linarith
      rw [h_sub_set]
      have h_m := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Icc T (2 * T)))
        (ae_of_all _ fun t => by dsimp only [F_t]; positivity) hF_int ((V / 4) ^ (2 * k))
      simpa [Measure.restrict_apply (hF_cont.measurable (measurableSet_le measurable_const measurable_id) :
        MeasurableSet { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t }), Set.inter_comm] using h_m
    have h_mom_bd := h_mom q χ Δ T k M hq hΔ_ge_Δ₀ (by linarith) hXk_le_T hM_diff hM_L1d hM_L1t
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_base : (4 / V) ^ 2 * (B * k * Real.log (Real.log X)) ≤
        (16 * B * (2 * Real.pi * K_scale)) * Real.log (Real.log T) / V := by
      calc (4 / V) ^ 2 * (B * k * Real.log (Real.log X))
          ≤ (16 / V ^ 2) * (B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log T)) := by
            gcongr; ring_nf; rfl
        _ = (8 * B / (Real.pi * K_scale)) * Real.log (Real.log T) / V := by
            field_simp [hV_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ (16 * B * (2 * Real.pi * K_scale)) * Real.log (Real.log T) / V := by
            gcongr
            have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi]
            nlinarith [Real.two_le_pi]
    have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
    have h1 : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal ≤
        ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
      calc (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal
          ≤ (1 / T) * ((∫ t in Set.Icc T (2 * T), F_t t) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / T) * ∫ t in Set.Icc T (2 * T), F_t t) := by ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (B * k * Real.log (Real.log X)) ^ k := by gcongr
        _ = ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact h1.trans (pow_le_pow_left₀ (by positivity) h_base k)
  have h_bp := h_markov_branch h_hat_p (fun x => (M_plus x).re) hMp_real hMp_L1_diff hMp_L1 rfl
  have h_bm := h_markov_branch h_hat_m (fun x => (M_minus x).re) hMm_real hMm_L1_diff hMm_L1 rfl
  have h_div_v : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
      (C_B * Real.log (Real.log T) / V) ^ k := by
    have h_2_pow : (2 : ℝ) ≤ 2 ^ k := by
      have : 2 ≤ 2 ^ 2 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) hk_ge_2)
    calc (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal
        ≤ (1 / T) * ((volume S_p).toReal + (volume S_m).toReal) := by gcongr
      _ = (1 / T) * (volume S_p).toReal + (1 / T) * (volume S_m).toReal := by ring
      _ ≤ (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k +
            (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := add_le_add h_bp h_bm
      _ = 2 * (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by ring
      _ ≤ 2 ^ k * (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by gcongr
      _ = (C_B * Real.log (Real.log T) / V) ^ k := by
          rw [← mul_pow]; dsimp only [C_B]; ring_nf
  have h_ratio_le : C_B * Real.log (Real.log T) / V ≤ (Real.log (Real.log T) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A := le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log T) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log T) ≤ A * Real.log (Real.log T) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log T) / V) ^ 2 ≤ Real.log (Real.log T) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, hLLT_pos]
    calc C_B * Real.log (Real.log T) / V = Real.sqrt ((C_B * Real.log (Real.log T) / V) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (Real.log T) / V) := Real.sqrt_le_sqrt h_sq
      _ = (Real.log (Real.log T) / V) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h_log_ratio : (1 / 2 : ℝ) * Real.log (V / Real.log (Real.log T)) ≤ -Real.log (C_B * Real.log (Real.log T) / V) := by
    have h1 : Real.log (C_B * Real.log (Real.log T) / V) ≤ (1 / 2 : ℝ) * Real.log (Real.log (Real.log T) / V) := by
      calc Real.log (C_B * Real.log (Real.log T) / V)
          ≤ Real.log ((Real.log (Real.log T) / V) ^ (1 / 2 : ℝ)) := Real.log_le_log (by positivity) h_ratio_le
        _ = (1 / 2 : ℝ) * Real.log (Real.log (Real.log T) / V) := Real.log_rpow (by positivity) _
    have h2 : Real.log (Real.log (Real.log T) / V) = -Real.log (V / Real.log (Real.log T)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have h_exp_final : (C_B * Real.log (Real.log T) / V) ^ k ≤
      Real.exp (-((1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_l_ge_1 : 1 ≤ V / Real.log (Real.log T) := by
      rw [le_div_iff₀ hLLT_pos]; have : 1 ≤ A := by linarith; nlinarith
    have h_log_nonneg : 0 ≤ Real.log (V / Real.log (Real.log T)) := Real.log_nonneg h_l_ge_1
    have h_k_log : (1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)) ≤
        (k : ℝ) * (-Real.log (C_B * Real.log (Real.log T) / V)) := by
      calc (1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T))
          = (V / (4 * (2 * Real.pi * K_scale))) * ((1 / 2 : ℝ) * Real.log (V / Real.log (Real.log T))) := by ring
        _ ≤ (k : ℝ) * (-Real.log (C_B * Real.log (Real.log T) / V)) := by
            gcongr; linarith [hk_lb]
    linarith
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log T) ≤ Real.log (V / Real.log (Real.log T)) := by
    have h_v_eq : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]; field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log T) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge)))
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by have : 1 ≤ Real.log (Real.log T) := by linarith; nlinarith [h_ratio_ge])
      have h4 : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLT_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log T)) ^ (1 / 4 : ℝ) = 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log T) = Real.log ((Real.log (Real.log T)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLT_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log T / Real.log (Real.log T))) := Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le2 : Real.exp (-((1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)))) ≤
      Real.exp (-c * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log T) = α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log T))]
      have h_32 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) * Real.log (Real.log T) = (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log T))]
        rw [← Real.rpow_add hLLT_pos]; norm_num
      nlinarith [h_32]
    dsimp only [c]
    nlinarith [hV_pos]
  rw [← div_le_iff₀' hT_pos]
  rw [one_div_mul_eq_div] at h_div_v
  exact h_div_v.trans (h_exp_final.trans h_exp_le2)

end PolarEvaluation
