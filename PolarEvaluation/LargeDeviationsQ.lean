import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments
import PolarEvaluation.TotientStar

/-!
# Large-Deviation Bounds in the q-Aspect (Theorem 1.5)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Classical

namespace PolarEvaluation

private lemma q_aspect_polar_ld_core (D : LFunctionData) (t₀ θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c A : ℝ), c > 0 ∧ A > 1 ∧
      ∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          ∀ V : ℝ, A * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) := by
  obtain ⟨C₀, hC₀, h_hzs⟩ := horizontal_zero_sum_external D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C_sup, C_L1, C_err_M, hΔ₀, hC_sup, hC_L1, hC_err_M, h_maj⟩ := asymmetric_majorant θ hθ
  have hK_int := kernelK_integrable θ
  have hK_int_val : ∫ x : ℝ, kernelK θ x = -Real.pi * Real.cos θ := kernelK_integral_eq θ
  let C_L1_tot : ℝ := max C_L1 (2 * envelopeC θ + C_err_M + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds θ C_L1_tot Δ₀ hθ.le hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_q_aspect θ C_L1_tot Δ₀ hθ.le hΔ₀
  have hC_env : 0 < envelopeC θ := envelopeC_pos hθ
  let K_scale : ℝ := max 1 (2 * envelopeC θ / Real.pi)
  have hK_scale_pos : 0 < K_scale := by positivity
  let C_B : ℝ := 16 * Real.exp 61 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (320 * (2 * Real.pi * K_scale) + 1)
    (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8))))
  have hA_gt_1 : A > 1 := by
    linarith [le_max_left (2 : ℝ) (max (320 * (2 * Real.pi * K_scale) + 1)
      (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8))))]
  let L_min : ℝ := max (max 100 (Real.pi * Δ₀ / K_scale + 1)) (max (16 * Real.pi * K_scale) 10)
  let q₀ : ℕ := max (Nat.ceil (|t₀| + 2) + 3) (Nat.ceil (Real.exp (Real.exp L_min)) + 3)
  let c : ℝ := 3 / (64 * (2 * Real.pi * K_scale))
  refine ⟨c, A, by positivity, hA_gt_1, q₀, le_trans (by omega) (le_max_left _ _), ?_⟩
  intro q hq1 hq_ge hqstar hGRH_all V hV_lb hV_ub
  have hq_ge_3 : q ≥ 3 := by omega
  have hq_pos : (0 : ℝ) < q := by positivity
  have hq_ge_exp : Real.exp (Real.exp L_min) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.exp L_min)) + 3 ≤ q := le_trans (le_max_right _ _) hq_ge
    have h2 : Real.exp (Real.exp L_min) ≤ (Nat.ceil (Real.exp (Real.exp L_min)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (Real.exp L_min)) : ℝ) ≤ q := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp L_min)) ≤ q)
    linarith
  have hlogq_ge_exp : Real.exp L_min ≤ Real.log q := by
    rw [← Real.log_exp (Real.exp L_min)]; exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hLLq_ge : L_min ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp L_min]; exact Real.log_le_log (Real.exp_pos _) hlogq_ge_exp
  have hLLq_ge_10 : 10 ≤ Real.log (Real.log q) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLLq_ge
  have hLLq_pos : 0 < Real.log (Real.log q) := by linarith
  have hlogq_pos : 0 < Real.log q := by linarith [Real.exp_pos L_min]
  have ht0_le_q : |t₀| + 2 ≤ (q : ℝ) := by
    have h1 : Nat.ceil (|t₀| + 2) + 3 ≤ q := le_trans (le_max_left _ _) hq_ge
    have h2 : |t₀| + 2 ≤ (Nat.ceil (|t₀| + 2) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (|t₀| + 2) : ℝ) ≤ q := by exact_mod_cast (by omega : Nat.ceil (|t₀| + 2) ≤ q)
    linarith
  have hac_le_q2 : analyticConductor q t₀ ≤ (q : ℝ) ^ 2 := by
    unfold analyticConductor; nlinarith
  have hac_ge_q : (q : ℝ) ≤ analyticConductor q t₀ := by
    unfold analyticConductor; have : 2 ≤ |t₀| + 2 := by linarith [abs_nonneg t₀]
    nlinarith
  have hlog_ac_le : Real.log (analyticConductor q t₀) ≤ 2 * Real.log q := by
    have h1 : Real.log (analyticConductor q t₀) ≤ Real.log ((q : ℝ) ^ 2) :=
      Real.log_le_log (by unfold analyticConductor; positivity) hac_le_q2
    rwa [Real.log_pow] at h1
  have hlog_ac_ge : Real.log q ≤ Real.log (analyticConductor q t₀) :=
    Real.log_le_log hq_pos hac_ge_q
  have hV_pos : 0 < V := by
    have : 0 < A := by linarith
    nlinarith
  let Δ : ℝ := K_scale * Real.log (analyticConductor q t₀) / V
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log q) ≤ Δ := by
      dsimp only [Δ]; rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
      calc K_scale * Real.log (Real.log q) * V = K_scale * (V * Real.log (Real.log q)) := by ring
        _ ≤ K_scale * Real.log q := by gcongr
        _ ≤ K_scale * Real.log (analyticConductor q t₀) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log q) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log q) :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLLq_ge
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log q / 2 := by
    rw [hlogX_eq]
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by
          dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log q := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log q := by gcongr; rw [div_le_iff₀ hV_pos]; linarith
      _ = Real.log q / 2 := by ring
  have hX_le_q : X ≤ (q : ℝ) := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hq_pos, Real.log_exp]; linarith [hlogX_le_half, hlogX_eq]
  have hlogX_pos : 0 < Real.log X := by rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor ((3 / 4 : ℝ) * (Real.log q / Real.log X))
  have hk_ge_1 : 1 ≤ k := by
    have h1 : (3 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := by
      have : 2 ≤ Real.log q / Real.log X := by rw [le_div_iff₀ hlogX_pos]; linarith
      linarith
    exact Nat.le_floor (by linarith)
  have hk_pos : 0 < k := by omega
  have hXk_lt_q : X ^ k < (q : ℝ) := by
    rw [← Real.log_lt_log_iff (pow_pos (Real.exp_pos _) _) hq_pos, Real.log_pow]
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h1 : (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * Real.log q := by
      calc (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) * Real.log X := by gcongr
        _ = (3 / 4 : ℝ) * Real.log q := by field_simp [hlogX_pos.ne']
    linarith
  have hk_lb : (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
    have h_lt : (3 / 4 : ℝ) * (Real.log q / Real.log X) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log q / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by
            dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log q / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log q / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    have h_34 : (3 / 4 : ℝ) * (V / (4 * Real.pi * K_scale)) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := by
      gcongr
    have h_ge3 : 3 ≤ (3 / 4 : ℝ) * (V / (4 * Real.pi * K_scale)) := by
      rw [← div_le_iff₀ (by positivity : (0 : ℝ) < 3 / 4)]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h_k2 : (1 / 2 : ℝ) * ((3 / 4 : ℝ) * (Real.log q / Real.log X)) ≤ (k : ℝ) := by linarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h_lx : 2 * Real.pi * K_scale * Real.log q / V ≤ Real.log X := by
      rw [hlogX_eq]; dsimp only [Δ]
      calc 2 * Real.pi * K_scale * Real.log q / V
          ≤ 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log (analyticConductor q t₀) / V) := by ring
    calc (k : ℝ) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := hk_le
      _ ≤ Real.log q / Real.log X := by linarith [div_nonneg hlogq_pos.le hlogX_pos.le]
      _ ≤ Real.log q / (2 * Real.pi * K_scale * Real.log q / V) :=
          div_le_div_of_nonneg_left hlogq_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by
          field_simp [hlogq_pos.ne', hK_scale_pos.ne', Real.pi_ne_zero]; ring
  obtain ⟨α, M_entire, hα, hM_exp, hM_real, hM_int, hM_sup, hM_L1, hM_maj, hM_err⟩ := h_maj Δ hΔ_ge_Δ₀
  let h_hat := fourierHat (fun x : ℝ => (majorantM θ Δ α x : ℂ))
  have hM_L1_diff : ∫ x : ℝ, |majorantM θ Δ α x - kernelK θ x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |majorantM θ Δ α x - kernelK θ x| = ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx))
    rw [h_eq]
    have h1 : ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x) ≤ 2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ) := by
      linarith [(abs_le.mp hM_err).2]
    have h2 : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
      have he := Real.add_one_le_exp (2 * Real.pi * Δ)
      have h3 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [Real.two_le_pi]
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3.trans_eq (one_mul _).symm
    have h3 : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
    calc ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x)
        ≤ 2 * envelopeC θ / Δ + C_err_M * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h3 hC_err_M.le]
      _ = (2 * envelopeC θ + C_err_M) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right C_L1 _)
  have hM_L1_tot : ∫ x : ℝ, |majorantM θ Δ α x| ≤ C_L1_tot :=
    h_L1.trans (le_max_left _ _)
  have h_tail_bd := h_tail q
  let S_target := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)
  let S_large := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ |primeSum1 q χ h_hat X t₀| ≥ V / 4)
  have h_subset : S_target ⊆ S_large := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ ⊢
    rcases hχ with ⟨_, hχ_prim, hχ_nv, hχ_pol⟩
    refine ⟨Finset.mem_univ _, hχ_prim, ?_⟩
    have hGRH := hGRH_all χ hχ_prim
    have hq1_t : q = 1 → |t₀| ≥ 10 := fun hq_eq1 => by omega
    obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs q hq1 χ hχ_prim hGRH θ hθ t₀ hχ_nv hq1_t
    have hM_im : ∀ x : ℝ, (M_entire x).im = 0 := fun x => (hM_real x).1
    have hM_sup_bd : ∀ x : ℝ, ‖M_entire x‖ ≤ (C_sup * Real.log Δ) / (1 + x ^ 2) := by
      intro x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre, Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (by positivity : 0 < 1 + x ^ 2), mul_comm]
      exact hM_sup x
    obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq1 χ hχ_prim hGRH M_entire Δ (C_sup * Real.log Δ)
      hΔ_ge_1 (mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)) hM_exp hM_sup_bd hM_im t₀ hq1_t
    have h_sum_le : ∑' n : ℕ, kernelK θ (t₀ - D.zeros q χ n) ≤ ∑' n : ℕ, (M_entire (t₀ - D.zeros q χ n)).re := by
      refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
      rw [(hM_real _).2]; exact hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t₀ hχ_nv n))
    have hM_int_re : (∫ x : ℝ, (M_entire x).re) = (∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ) := by
      have heq_M : (fun x : ℝ => (M_entire x).re) = fun x => majorantM θ Δ α x := funext fun x => (hM_real x).2
      rw [heq_M, ← hK_int_val, ← integral_add hM_int hK_int]
      congr 1; ext x; ring
    have h_hat_eq : fourierHat (fun x : ℝ => M_entire x) = h_hat := by
      ext ξ; unfold fourierHat; congr 1; ext x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre]
    rw [h_hat_eq] at h_gw_bd
    set Q : ℝ := analyticConductor q t₀
    have hQ_ge_100 : 100 ≤ Q := by
      have h_q100 : (100 : ℝ) ≤ q := by
        have : (100 : ℝ) ≤ Real.exp (Real.exp 100) := by
          have : (100 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
          linarith [Real.add_one_le_exp (Real.exp 100)]
        have : Real.exp (Real.exp 100) ≤ Real.exp (Real.exp L_min) :=
          Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (le_trans (le_max_left _ _) (le_max_left _ _)))
        linarith
      exact h_q100.trans hac_ge_q
    have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_entire x).re) ≤
        -(Real.cos θ / 2) * Real.log Q + envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
        (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) := by
      rw [hM_int_re]
      have h1 : ∫ x : ℝ, majorantM θ Δ α x - kernelK θ x ≤ 2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ) := by
        linarith [(abs_le.mp hM_err).2]
      have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
      calc (Real.log Q / (2 * Real.pi)) * ((∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ))
          ≤ (Real.log Q / (2 * Real.pi)) * ((2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ)) + (-Real.pi * Real.cos θ)) := by
            gcongr
        _ = _ := by field_simp [Real.pi_ne_zero]; ring
    have h_env_le : envelopeC θ * (Real.log Q / (Real.pi * Δ)) ≤ V / 2 := by
      have h_k : 2 * envelopeC θ / Real.pi ≤ K_scale := le_max_right _ _
      calc envelopeC θ * (Real.log Q / (Real.pi * Δ))
          = (envelopeC θ / (Real.pi * K_scale)) * V := by
            dsimp only [Δ, Q]; field_simp [Real.pi_ne_zero, hK_scale_pos.ne', hV_pos.ne']; ring
        _ ≤ (1 / 2 : ℝ) * V := by
            gcongr; rw [div_le_iff₀ (by positivity)]; linarith
        _ = V / 2 := by ring
    have h_exp_err : (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) ≤ C_err_M * Real.log (Real.log q) := by
      have h_2piΔ : Real.log (Real.log q) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
        have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
        calc Real.log (Real.log q) ≤ Real.pi * K_scale * Real.log (Real.log q) := le_mul_of_one_le_left hLLq_pos.le h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log Q / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log q) * V = Real.pi * K_scale * (V * Real.log (Real.log q)) := by ring
                _ ≤ Real.pi * K_scale * Real.log q := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log Q := by
                    nlinarith [hlog_ac_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log q := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogq_pos (by
          calc Real.log q = Real.exp (Real.log (Real.log q)) := (Real.exp_log hlogq_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      calc (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ))
          ≤ (2 * Real.log q / (2 * Real.pi)) * (C_err_M * (1 / Real.log q)) := by gcongr
        _ = C_err_M / Real.pi := by field_simp [hlogq_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ C_err_M * Real.log (Real.log q) := by
            have : 1 / Real.pi ≤ Real.log (Real.log q) := by
              have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
              linarith
            nlinarith [hC_err_M]
    have h_gw_err : C₁ * (C_sup * Real.log Δ +
        (if q = 1 then Real.exp (Real.pi * Δ) / t₀ ^ 2 * (C_sup * Real.log Δ) else 0)) ≤
        2 * C₁ * C_sup * Real.log (Real.log q) := by
      have hΔ_le_q : Δ ≤ Real.log q := by
        dsimp only [Δ]
        calc K_scale * Real.log (analyticConductor q t₀) / V ≤ K_scale * (2 * Real.log q) / V := by gcongr
          _ = (2 * K_scale / V) * Real.log q := by ring
          _ ≤ 1 * Real.log q := by
              gcongr
              rw [div_le_one hV_pos]
              have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
                le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
              have h_a : 2 ≤ A := le_max_left _ _
              nlinarith [Real.two_le_pi]
          _ = Real.log q := one_mul _
      have h_logΔ : Real.log Δ ≤ Real.log (Real.log q) := Real.log_le_log hΔ_pos hΔ_le_q
      rw [if_neg (by omega : q ≠ 1), add_zero]
      nlinarith
    have h_tail_t := h_tail_bd χ h_hat Δ (majorantM θ Δ α) hΔ_ge_Δ₀ hM_int hM_L1_diff hM_L1_tot t₀
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_P_split : primePowerSum q χ h_hat X t₀ =
        primeSum1 q χ h_hat X t₀ + primeSum2 q χ h_hat X t₀ + primeSumGe3 q χ h_hat X t₀ := by
      unfold primeSumGe3; ring
    have h_p23 : |primeSum2 q χ h_hat X t₀ + primeSumGe3 q χ h_hat X t₀| ≤ 2 * C_tail * Real.log (Real.log q) := by
      have h1 : |primeSum2 q χ h_hat X t₀| ≤ C_tail * Real.log (Real.log q) :=
        h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
      have h2 : |primeSumGe3 q χ h_hat X t₀| ≤ C_tail * Real.log (Real.log q) :=
        h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
      linarith [abs_add_le (primeSum2 q χ h_hat X t₀) (primeSumGe3 q χ h_hat X t₀)]
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log q) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log q) + C₀ + 2 * C₁ * C_sup * Real.log (Real.log q) +
        C_err_M * Real.log (Real.log q) ≤ V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      nlinarith
    have h_pol_le : V ≤ V / 2 - primeSum1 q χ h_hat X t₀ + V / 4 := by
      have h_g := (abs_le.mp h_gw_bd).2
      have h_h := (abs_le.mp h_hzs_bd).2
      have h_p := (abs_le.mp h_p23).1
      linarith
    have h_neg : -primeSum1 q χ h_hat X t₀ ≥ V / 4 := by linarith
    exact le_trans h_neg (neg_le_abs _)
  have h_card_le : (S_target.card : ℝ) ≤ (S_large.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_subset
  let S_prim := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  have h_markov : (V / 4) ^ (2 * k) * (S_large.card : ℝ) ≤
      ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
    have h_sub_prim : S_large ⊆ S_prim := by
      intro χ hχ; rw [Finset.mem_filter] at hχ ⊢; exact ⟨Finset.mem_univ _, hχ.2.1⟩
    calc (V / 4) ^ (2 * k) * (S_large.card : ℝ)
        = ∑ _χ ∈ S_large, (V / 4) ^ (2 * k) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ χ ∈ S_large, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          rw [Finset.mem_filter] at hχ
          exact pow_le_pow_left₀ (by positivity) hχ.2.2 (2 * k)
      _ ≤ ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub_prim (fun _ _ _ => by positivity)
  have h_mom_bd := h_mom q t₀ Δ k (majorantM θ Δ α) hq_ge_3 hqstar hΔ_ge_Δ₀ hXk_lt_q hM_int hM_L1_diff hM_L1_tot
  have h_tot_star : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤ (2 * Real.exp 61) ^ k := by
    have h_t1 := totient_div_totientStar_le q hq_ge_3 hqstar
    have h_30_le_k : 30 * Real.log (Real.log q) ≤ (k : ℝ) := by
      have h_a : 320 * (2 * Real.pi * K_scale) + 1 ≤ A :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have h_k1 : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
        calc (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale))
            ≤ (3 : ℝ) * (A * Real.log (Real.log q)) / (16 * (2 * Real.pi * K_scale)) := by gcongr; linarith
          _ ≤ (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) := by gcongr
          _ ≤ (k : ℝ) := hk_lb
      have h_eq : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) =
          60 * Real.log (Real.log q) := by
        field_simp [hK_scale_pos.ne', Real.pi_ne_zero]; ring
      linarith
    have h_logq_pow : (Real.log q) ^ 30 ≤ Real.exp k := by
      calc (Real.log q) ^ 30 = Real.exp ((30 : ℕ) * Real.log (Real.log q)) := by
            rw [← Real.log_pow, Real.exp_log (pow_pos hlogq_pos 30)]
        _ ≤ Real.exp (k : ℝ) := by push_cast; exact Real.exp_le_exp.mpr h_30_le_k
    have h_c_pow : 2 * Real.exp 60 ≤ (2 * Real.exp 60) ^ k :=
      le_self_pow₀ (by have : 1 ≤ Real.exp 60 := Real.one_le_exp (by norm_num); linarith) hk_pos.ne'
    have h_exp_k : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
      rw [← Real.exp_nat_mul, mul_one]
    calc (Nat.totient q : ℝ) / (totientStar q : ℝ)
        ≤ 2 * Real.exp 60 * (Real.log q) ^ 30 := h_t1
      _ ≤ (2 * Real.exp 60) ^ k * (Real.exp 1) ^ k := by gcongr; rwa [← h_exp_k]
      _ = (2 * Real.exp 60 * Real.exp 1) ^ k := (mul_pow _ _ _).symm
      _ = (2 * Real.exp 61) ^ k := by
          congr 1; rw [mul_assoc, ← Real.exp_add]; norm_num
  have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
    Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
  have h_base : (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X)) ≤
      C_B * Real.log (Real.log q) / V := by
    calc (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))
        ≤ (16 / V ^ 2) * (2 * Real.exp 61 * B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log q)) := by
          gcongr; ring_nf; rfl
      _ = (16 * Real.exp 61 * B / (Real.pi * K_scale)) * Real.log (Real.log q) / V := by
          field_simp [hV_pos.ne', Real.pi_ne_zero, hK_scale_pos.ne']; ring
      _ ≤ C_B * Real.log (Real.log q) / V := by
          gcongr
          dsimp only [C_B]
          have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
          have : 0 ≤ 16 * Real.exp 61 * B := by positivity
          nlinarith [Real.two_le_pi]
  have h_div_v : (1 / (totientStar q : ℝ)) * (S_target.card : ℝ) ≤
      (C_B * Real.log (Real.log q) / V) ^ k := by
    have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
    have hqstar_pos : (0 : ℝ) < totientStar q := by exact_mod_cast hqstar
    have h1 : (1 / (totientStar q : ℝ)) * (S_large.card : ℝ) ≤
        ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
      calc (1 / (totientStar q : ℝ)) * (S_large.card : ℝ)
          ≤ (1 / (totientStar q : ℝ)) * ((∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / (totientStar q : ℝ)) * ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) := by
            ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (((Nat.totient q : ℝ) / (totientStar q : ℝ)) * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr; exact h_mom_bd
        _ ≤ (1 / (V / 4) ^ (2 * k)) * ((2 * Real.exp 61) ^ k * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ = ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact (mul_le_mul_of_nonneg_left h_card_le (by positivity)).trans (h1.trans (pow_le_pow_left₀ (by positivity) h_base k))
  have h_ratio_le : C_B * Real.log (Real.log q) / V ≤ (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A :=
      le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log q) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log q) ≤ A * Real.log (Real.log q) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log q) / V) ^ 2 ≤ Real.log (Real.log q) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, hLLq_pos]
    calc C_B * Real.log (Real.log q) / V = Real.sqrt ((C_B * Real.log (Real.log q) / V) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (Real.log q) / V) := Real.sqrt_le_sqrt h_sq
      _ = (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h_log_ratio : (1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q)) ≤ -Real.log (C_B * Real.log (Real.log q) / V) := by
    have h1 : Real.log (C_B * Real.log (Real.log q) / V) ≤ (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := by
      calc Real.log (C_B * Real.log (Real.log q) / V)
          ≤ Real.log ((Real.log (Real.log q) / V) ^ (1 / 2 : ℝ)) := Real.log_le_log (by positivity) h_ratio_le
        _ = (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := Real.log_rpow (by positivity) _
    have h2 : Real.log (Real.log (Real.log q) / V) = -Real.log (V / Real.log (Real.log q)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have h_exp_final : (C_B * Real.log (Real.log q) / V) ^ k ≤
      Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_v_log : 0 ≤ Real.log (V / Real.log (Real.log q)) := by
      apply Real.log_nonneg; rw [one_le_div hLLq_pos]; have : 1 ≤ A := by linarith; nlinarith
    calc (k : ℝ) * Real.log (C_B * Real.log (Real.log q) / V)
        ≤ (k : ℝ) * (-(1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q))) := by gcongr; linarith
      _ = -(1 / 2 : ℝ) * (k : ℝ) * Real.log (V / Real.log (Real.log q)) := by ring
      _ ≤ -(1 / 2 : ℝ) * ((3 : ℝ) * V / (16 * (2 * Real.pi * K_scale))) * Real.log (V / Real.log (Real.log q)) := by
          gcongr
      _ ≤ -c * V * Real.log (V / Real.log (Real.log q)) := by
          dsimp only [c]; ring_nf; linarith [mul_nonneg hV_pos.le h_v_log]
  exact h_div_v.trans h_exp_final

/-- **Theorem 1.5** (`q`-aspect large-deviation bound). -/
theorem q_aspect_large_deviation (D : LFunctionData) (t₀ θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c c' A : ℝ), c > 0 ∧ c' > 0 ∧ A > 1 ∧
      (∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          ∀ V : ℝ, A * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c * V * Real.log (V / Real.log (Real.log q)))) ∧
      (∀ α : ℝ, α > 0 → ∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          let V := α * Real.sqrt (Real.log q * Real.log (Real.log q))
          V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c' * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ))) := by
  obtain ⟨c, A, hc, hA, q₀₁, hq₀₁, h_part1⟩ := q_aspect_polar_ld_core D t₀ θ hθ
  refine ⟨c, c / 4, A, hc, by positivity, hA, ⟨q₀₁, hq₀₁, h_part1⟩, fun α hα => ?_⟩
  let L_α : ℝ := max 100 (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))
  let q₀ : ℕ := max q₀₁ (Nat.ceil (Real.exp (Real.exp L_α)) + 3)
  refine ⟨q₀, le_trans hq₀₁ (le_max_left _ _), fun q hq1 hq_ge hqstar hGRH_all V hV_ub => ?_⟩
  have hq_ge_q₀₁ : q ≥ q₀₁ := le_trans (le_max_left _ _) hq_ge
  have hq_ge_exp : Real.exp (Real.exp L_α) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.exp L_α)) + 3 ≤ q := le_trans (le_max_right _ _) hq_ge
    have h2 : Real.exp (Real.exp L_α) ≤ (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) ≤ q := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp L_α)) ≤ q)
    linarith
  have hlogq_ge_exp : Real.exp L_α ≤ Real.log q := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hLLq_ge : L_α ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogq_ge_exp
  have hLLq_pos : 0 < Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
  have hlogq_pos : 0 < Real.log q := by linarith [Real.exp_pos L_α]
  have h_ratio_le : (Real.log q / Real.log (Real.log q)) ≥ (Real.log (Real.log q)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log q)) hLLq_pos.le 4
    have h3 : (Real.log (Real.log q)) ^ 4 / 24 ≤ Real.log q := by
      calc (Real.log (Real.log q)) ^ 4 / 24 = (Real.log (Real.log q)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log q)) := he4
        _ = Real.log q := Real.exp_log hlogq_pos
    have h_llq : 24 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
    rw [ge_iff_le, le_div_iff₀ hLLq_pos]; nlinarith [pow_nonneg hLLq_pos.le 3]
  have hV_lb : A * Real.log (Real.log q) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log q) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLq_ge)
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log q)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log q)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log q) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt h_ratio_le
    have h4 : A / α ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have : 1 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
      calc A / α ≤ Real.sqrt (Real.log (Real.log q)) := h2
        _ ≤ Real.log (Real.log q) := by rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := h3
    have h5 : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    rw [← div_le_iff₀ hLLq_pos, h5, ← div_le_iff₀' hα]; exact h4
  have h_p1 := h_part1 q hq1 hq_ge_q₀₁ hqstar hGRH_all V hV_lb hV_ub
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log q) ≤ Real.log (V / Real.log (Real.log q)) := by
    have h_v_eq : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log q) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge)
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by have : 1 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]; nlinarith [h_ratio_le])
      have h4 : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLq_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log q)) ^ (1 / 4 : ℝ) = 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log q) = Real.log ((Real.log (Real.log q)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLq_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log q / Real.log (Real.log q))) := Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le : Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) ≤
      Real.exp (-(c / 4) * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log q) = α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log q))]
      have h_32 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) * Real.log (Real.log q) = (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log q))]
        rw [← Real.rpow_add hLLq_pos]; norm_num
      nlinarith [h_32]
    nlinarith [mul_nonneg hc.le (show 0 ≤ V by dsimp only [V]; positivity)]
  exact h_p1.trans h_exp_le

end PolarEvaluation
