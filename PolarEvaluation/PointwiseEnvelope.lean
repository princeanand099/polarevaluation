import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice

/-!
# Pointwise Polar Envelope and Universal Convex Domain (Section 5 & Theorems 1.1–1.2, Corollary 1.3)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- Helper: `log(log(log x)) / log(log x) < δ` for sufficiently large `x`. -/
lemma logloglog_div_loglog_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℝ, Q ≥ 100 ∧ ∀ x : ℝ, x ≥ Q →
      0 < Real.log (Real.log x) ∧
      Real.log (Real.log (Real.log x)) / Real.log (Real.log x) < δ := by
  have hM : 0 < (2 / δ) ^ 2 + 10 := by positivity
  refine ⟨max 100 (Real.exp (Real.exp ((2 / δ) ^ 2 + 10))), le_max_left _ _, fun x hx => ?_⟩
  have h1 : Real.exp (Real.exp ((2 / δ) ^ 2 + 10)) ≤ x := le_trans (le_max_right _ _) hx
  have h2 : Real.exp ((2 / δ) ^ 2 + 10) ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp ((2 / δ) ^ 2 + 10))]
    exact Real.log_le_log (Real.exp_pos _) h1
  have h3 : (2 / δ) ^ 2 + 10 ≤ Real.log (Real.log x) := by
    rw [← Real.log_exp ((2 / δ) ^ 2 + 10)]
    exact Real.log_le_log (Real.exp_pos _) h2
  have hloglog_pos : 0 < Real.log (Real.log x) := by linarith
  refine ⟨hloglog_pos, ?_⟩
  have hlog_le : Real.log (Real.log (Real.log x)) ≤ 2 * Real.sqrt (Real.log (Real.log x)) := by
    have hr := Real.log_le_rpow_div hloglog_pos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    linarith
  have hsqrt_gt : 2 / δ < Real.sqrt (Real.log (Real.log x)) := by
    rw [Real.lt_sqrt (by positivity)]
    linarith
  calc Real.log (Real.log (Real.log x)) / Real.log (Real.log x)
      ≤ (2 * Real.sqrt (Real.log (Real.log x))) / Real.log (Real.log x) :=
        div_le_div_of_nonneg_right hlog_le hloglog_pos.le
    _ = 2 / Real.sqrt (Real.log (Real.log x)) := by
        have hs : 0 < Real.sqrt (Real.log (Real.log x)) := Real.sqrt_pos.mpr hloglog_pos
        have hsq : Real.sqrt (Real.log (Real.log x)) * Real.sqrt (Real.log (Real.log x)) = Real.log (Real.log x) := Real.mul_self_sqrt hloglog_pos.le
        conv_lhs => rhs; rw [← hsq]
        field_simp [hs.ne']
    _ < 2 / (2 / δ) := div_lt_div_of_pos_left two_pos (by positivity) hsqrt_gt
    _ = δ := by field_simp [hδ.ne']

/-- Helper: `scale(x) = log x / log(log x) > 0` for `x ≥ 100`. -/
lemma scale_pos_of_ge_100 {x : ℝ} (hx : 100 ≤ x) :
    0 < Real.log x / Real.log (Real.log x) := by
  have h1 : Real.log x ≥ Real.log 100 := Real.log_le_log (by norm_num) hx
  have h2 : Real.log 100 > Real.exp 1 := by
    have : (100 : ℝ) > Real.exp (Real.exp 1) := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      calc Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he
      _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ < 3 * 3 * 3 := by gcongr
      _ < 100 := by norm_num
    linarith [Real.log_lt_log (by positivity) this, Real.log_exp (Real.exp 1)]
  have hlog_pos : 0 < Real.log x := by linarith [Real.exp_pos 1]
  have hloglog_pos : 0 < Real.log (Real.log x) := by
    apply Real.log_pos
    linarith [Real.one_lt_exp_iff.mpr one_pos]
  positivity

lemma sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hstep : (1 : ℝ) / Real.sqrt (k + 1 : ℕ) ≤ 2 * (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) := by
      have hk1 : (0 : ℝ) < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
      have hdiff : Real.sqrt (k + 1 : ℕ) ^ 2 - Real.sqrt k ^ 2 = 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        push_cast; ring
      have hfac : (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * (Real.sqrt (k + 1 : ℕ) + Real.sqrt k) = 1 := by
        linarith [hdiff]
      have hsum_le : Real.sqrt (k + 1 : ℕ) + Real.sqrt k ≤ 2 * Real.sqrt (k + 1 : ℕ) := by
        have : Real.sqrt k ≤ Real.sqrt (k + 1 : ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
        linarith
      have hsum_pos : 0 < Real.sqrt (k + 1 : ℕ) + Real.sqrt k := by positivity
      calc (1 : ℝ) / Real.sqrt (k + 1 : ℕ)
          ≤ 2 / (Real.sqrt (k + 1 : ℕ) + Real.sqrt k) := by
            rw [div_le_div_iff₀ hk1 hsum_pos]; linarith
        _ = 2 * (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) := by
            rw [← hfac]; field_simp [hsum_pos.ne']; ring
    linarith

lemma primePowerSum_abs_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (h_hat : ℝ → ℂ)
    (B X t : ℝ) (hB : 0 ≤ B) (hX : 2 ≤ X) (h_bd : ∀ ξ : ℝ, ‖h_hat ξ‖ ≤ B) :
    |primePowerSum q χ h_hat X t| ≤ (2 * B / Real.pi) * Real.log X * Real.sqrt X := by
  unfold primePowerSum
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hsum_le : |∑ n ∈ Finset.Icc 2 (Nat.floor X),
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
         star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re| ≤
      4 * B * Real.log X * Real.sqrt X := by
    calc |∑ n ∈ Finset.Icc 2 (Nat.floor X), _|
        ≤ ∑ n ∈ Finset.Icc 2 (Nat.floor X),
            |((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
              (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
               star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 (Nat.floor X), (2 * B * Real.log X) * ((1 : ℝ) / Real.sqrt n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn_le : (n : ℝ) ≤ X := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
          have hlog_le : Real.log n ≤ Real.log X := Real.log_le_log (by positivity) hn_le
          have hvm_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
          have hvm_le : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log X :=
            ArithmeticFunction.vonMangoldt_le_log.trans hlog_le
          have hχ_norm : ‖χ n‖ ≤ 1 := by
            by_cases hunit : IsUnit (n : ZMod q)
            · have h1 := χ.norm_eq_one_of_isUnit hunit
              linarith
            · rw [MulChar.map_nonunit _ hunit, norm_zero]
              norm_num
          have hexp1 : ‖Complex.exp (-Complex.I * t * Real.log n)‖ = 1 := by
            have : -Complex.I * (t : ℂ) * Real.log n = ((-t * Real.log n : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.norm_exp_ofReal_mul_I]
          have hexp2 : ‖Complex.exp (Complex.I * t * Real.log n)‖ = 1 := by
            have : Complex.I * (t : ℂ) * Real.log n = ((t * Real.log n : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.norm_exp_ofReal_mul_I]
          have hre_le : |(χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
              star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re| ≤ 2 * B := by
            refine (Complex.abs_re_le_norm _).trans ?_
            refine (norm_add_le _ _).trans ?_
            have ht1 : ‖χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n)‖ ≤ B := by
              rw [norm_mul, norm_mul, hexp1, mul_one]
              calc ‖χ n‖ * ‖h_hat _‖ ≤ 1 * B := mul_le_mul hχ_norm (h_bd _) (norm_nonneg _) zero_le_one
                _ = B := one_mul B
            have ht2 : ‖star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)‖ ≤ B := by
              rw [norm_mul, norm_mul, hexp2, mul_one, norm_star]
              calc ‖χ n‖ * ‖h_hat _‖ ≤ 1 * B := mul_le_mul hχ_norm (h_bd _) (norm_nonneg _) zero_le_one
                _ = B := one_mul B
            linarith
          rw [abs_mul, abs_of_nonneg (div_nonneg hvm_nonneg (Real.sqrt_nonneg _))]
          calc ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * |_.re|
              ≤ (Real.log X / Real.sqrt n) * (2 * B) := by
                gcongr
            _ = (2 * B * Real.log X) * ((1 : ℝ) / Real.sqrt n) := by ring
      _ = (2 * B * Real.log X) * ∑ n ∈ Finset.Icc 2 (Nat.floor X), (1 : ℝ) / Real.sqrt n := by
          rw [← Finset.mul_sum]
      _ ≤ (2 * B * Real.log X) * (2 * Real.sqrt (Nat.floor X)) := by
          gcongr
          have hsub : Finset.Icc 2 (Nat.floor X) ⊆ Finset.Icc 1 (Nat.floor X) := by
            intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
            (sum_inv_sqrt_le (Nat.floor X))
      _ ≤ (2 * B * Real.log X) * (2 * Real.sqrt X) := by
          gcongr
          exact Nat.floor_le (by positivity)
      _ = 4 * B * Real.log X * Real.sqrt X := by ring
  calc (1 / (2 * Real.pi)) * |∑ n ∈ Finset.Icc 2 (Nat.floor X), _|
      ≤ (1 / (2 * Real.pi)) * (4 * B * Real.log X * Real.sqrt X) := by gcongr
    _ = (2 * B / Real.pi) * Real.log X * Real.sqrt X := by ring

/-- **Theorem 1.1** (Pointwise directional envelope). -/
theorem directional_envelope_bound (D : LFunctionData) (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Q₀ C_err : ℝ), Q₀ ≥ 100 ∧ C_err > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          polarLogL D q χ t θ ≤
            (envelopeC θ + C_err * Real.log (Real.log (Real.log (analyticConductor q t))) /
              Real.log (Real.log (analyticConductor q t))) *
              (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  obtain ⟨C₀, hC₀_pos, h_hzs⟩ := horizontal_zero_sum D
  obtain ⟨C₁, hC₁_pos, h_gw⟩ := guinand_weil_bandlimited D
  obtain ⟨Δ₀, C_sup, C_L1, C_err_M, hΔ₀, hC_sup, hC_L1, hC_err_M, h_maj⟩ := asymmetric_majorant θ hθ
  obtain ⟨Q_16, hQ_16, hlll_16⟩ := logloglog_div_loglog_lt (1 / 6) (by norm_num)
  let L₀ : ℝ := max 100 (2 * Real.pi * Δ₀ + 2 * Real.pi)
  let Q₀ : ℝ := max (max 100 Q_16) (Real.exp (Real.exp L₀))
  let C_err : ℝ := 6 * |envelopeC θ| + C_err_M / (2 * Real.pi) + 4 * C_L1 / Real.pi +
    2 * C₁ * C_sup + C₀ + 1
  refine ⟨Q₀, C_err, le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _)),
    by positivity, fun q hq χ hχ hGRH t ht hcond => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  set Q : ℝ := analyticConductor q t
  have hQ_ge_100 : 100 ≤ Q := le_trans (le_trans (by norm_num) (le_max_left _ _)) (le_trans (le_max_left _ _) hcond)
  have hQ_ge_Q16 : Q_16 ≤ Q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hcond)
  have hQ_ge_exp : Real.exp (Real.exp L₀) ≤ Q := le_trans (le_max_right _ _) hcond
  have hL_ge : L₀ ≤ Real.log (Real.log Q) := by
    have h1 : Real.exp L₀ ≤ Real.log Q := by
      rw [← Real.log_exp (Real.exp L₀)]
      exact Real.log_le_log (Real.exp_pos _) hQ_ge_exp
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) h1
  set L : ℝ := Real.log (Real.log Q)
  set LL : ℝ := Real.log L
  have hL_ge_100 : 100 ≤ L := le_trans (le_max_left _ _) hL_ge
  have hL_pos : 0 < L := by linarith
  have hLL_ge_1 : 1 ≤ LL := by
    have : Real.exp 1 ≤ 100 := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (this.trans hL_ge_100)
  have hLL_div_L : LL / L < 1 / 6 := (hlll_16 Q hQ_ge_Q16).2
  have h_piΔ_ge : L / 2 ≤ L - 3 * LL := by
    have : 3 * LL ≤ L / 2 := by
      have h1 : LL < (1 / 6) * L := (div_lt_iff₀ hL_pos).mp hLL_div_L
      linarith
    linarith
  set Δ : ℝ := (L - 3 * LL) / Real.pi
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have hL_ge_2pi : 2 * Real.pi * Δ₀ ≤ L / 2 := by
      have : 2 * Real.pi * Δ₀ + 2 * Real.pi ≤ L := le_trans (le_max_right _ _) hL_ge
      nlinarith [Real.pi_pos]
    dsimp only [Δ]
    rw [le_div_iff₀ Real.pi_pos]
    linarith
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  obtain ⟨α, M_entire, hα, hM_exp, hM_real, hM_int, hM_sup, hM_L1, hM_maj, hM_err⟩ := h_maj Δ hΔ_ge_Δ₀
  have hq1_t : q = 1 → |t| ≥ 10 := by
    intro hq1
    have : Q = |t| + 2 := by simp [Q, analyticConductor, hq1]
    linarith
  obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs q hq χ hχ hGRH θ hθ t ht hq1_t
  have hM_im : ∀ x : ℝ, (M_entire x).im = 0 := fun x => (hM_real x).1
  have hM_sup_bd : ∀ x : ℝ, ‖M_entire x‖ ≤ (C_sup * Real.log Δ) / (1 + x ^ 2) := by
    intro x
    have hnorm : ‖M_entire x‖ = |majorantM θ Δ α x| := by
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [(hM_real x).2]
        · simp [(hM_real x).1]
      rw [hre, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2), mul_comm]
    exact hM_sup x
  have hM_sup_nonneg : 0 ≤ C_sup * Real.log Δ :=
    mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)
  obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_entire Δ (C_sup * Real.log Δ)
    hΔ_ge_1 hM_sup_nonneg hM_exp hM_sup_bd hM_im t hq1_t
  have h_sum_le : ∑' n : ℕ, kernelK θ (t - D.zeros q χ n) ≤
      ∑' n : ℕ, (M_entire (t - D.zeros q χ n)).re := by
    refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
    have hne : t - D.zeros q χ n ≠ 0 := sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht n)
    rw [(hM_real _).2]
    exact hM_maj _ hne
  have hK_int_val : ∫ x : ℝ, kernelK θ x = -Real.pi * Real.cos θ := by
    have h0 := (kernelK_fourier θ hθ.le).1
    unfold fourierHat at h0
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h0
    have heq : (∫ x : ℝ, (kernelK θ x : ℂ)) = ((∫ x : ℝ, kernelK θ x : ℝ) : ℂ) := integral_ofReal
    rw [heq] at h0
    exact Complex.ofReal_injective (by simpa using h0)
  have hM_int_split : ∫ x : ℝ, (M_entire x).re =
      (∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ) := by
    have heq_M : (fun x : ℝ => (M_entire x).re) = fun x => majorantM θ Δ α x := funext fun x => (hM_real x).2
    rw [heq_M, ← hK_int_val]
    have hK_int := kernelK_integrable θ
    rw [← integral_add hM_int hK_int]
    congr 1; ext x; ring
  have h_gw_upper : ∑' n : ℕ, (M_entire (t - D.zeros q χ n)).re ≤
      (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_entire x).re) -
        primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) (Real.exp (2 * Real.pi * Δ)) t +
        C₁ * (C_sup * Real.log Δ +
          (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0)) := by
    linarith [(abs_le.mp h_gw_bd).2]
  have h_hzs_upper : polarLogL D q χ t θ ≤
      (Real.cos θ / 2) * Real.log Q + ∑' n : ℕ, kernelK θ (t - D.zeros q χ n) + C₀ := by
    linarith [(abs_le.mp h_hzs_bd).2]
  have h_main_int_bd : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_entire x).re) ≤
      -(Real.cos θ / 2) * Real.log Q +
        envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
        (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) := by
    rw [hM_int_split]
    have h_err_upper : ∫ x : ℝ, majorantM θ Δ α x - kernelK θ x ≤
        2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ) := by
      linarith [(abs_le.mp hM_err).2]
    have hlogQ_nonneg : 0 ≤ Real.log Q / (2 * Real.pi) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
    calc (Real.log Q / (2 * Real.pi)) * ((∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ))
        ≤ (Real.log Q / (2 * Real.pi)) * ((2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ)) + (-Real.pi * Real.cos θ)) := by
          gcongr
      _ = -(Real.cos θ / 2) * Real.log Q + envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
            (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) := by
          field_simp [Real.pi_ne_zero]; ring
  set X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hX_eq : X = Real.log Q ^ 2 / L ^ 6 := by
    dsimp only [X, Δ]
    rw [show 2 * Real.pi * ((L - 3 * LL) / Real.pi) = 2 * L - 6 * LL by field_simp [Real.pi_ne_zero]; ring,
      Real.exp_sub, Real.exp_nat_mul, show (6 : ℕ) * LL = 6 * LL by ring]
    simp only [L, LL]
    rw [Real.exp_log (by linarith), Real.exp_nat_mul, Real.exp_log hL_pos]
    ring
  have hX_ge_2 : 2 ≤ X := by
    have h1 : 1 ≤ 2 * Real.pi * Δ := by nlinarith [Real.pi_pos]
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h1
  have h_four_bd : ∀ ξ : ℝ, ‖fourierHat (fun x : ℝ => M_entire x) ξ‖ ≤ C_L1 := by
    intro ξ
    unfold fourierHat
    calc ‖∫ x : ℝ, M_entire x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖
        ≤ ∫ x : ℝ, ‖M_entire x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, |majorantM θ Δ α x| := by
          congr 1; ext x
          have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
            have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.norm_exp_ofReal_mul_I]
          have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [(hM_real x).1, (hM_real x).2]
          rw [norm_mul, hn, mul_one, hre, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ C_L1 := hM_L1
  have h_pps_bd : |primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t| ≤
      (2 * C_L1 / Real.pi) * Real.log X * Real.sqrt X :=
    primePowerSum_abs_le q χ _ C_L1 X t hC_L1.le hX_ge_2 h_four_bd
  have h_sqrt_X : Real.sqrt X = Real.log Q / L ^ 3 := by
    rw [hX_eq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by linarith),
      show L ^ 6 = (L ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h_log_X : Real.log X ≤ 2 * L := by
    dsimp only [X]
    rw [Real.log_exp]
    have : 2 * Real.pi * Δ = 2 * L - 6 * LL := by
      dsimp only [Δ]; field_simp [Real.pi_ne_zero]; ring
    linarith
  have h_pps_scale : |primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t| ≤
      (4 * C_L1 / Real.pi) * (LL / L) * (Real.log Q / L) := by
    have hlogX_nonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    calc |primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t|
        ≤ (2 * C_L1 / Real.pi) * Real.log X * Real.sqrt X := h_pps_bd
      _ ≤ (2 * C_L1 / Real.pi) * (2 * L) * (Real.log Q / L ^ 3) := by gcongr
      _ = (4 * C_L1 / Real.pi) * (1 / L) * (Real.log Q / L) := by
          field_simp [hL_pos.ne']; ring
      _ ≤ (4 * C_L1 / Real.pi) * (LL / L) * (Real.log Q / L) := by
          gcongr
          exact div_le_div_of_nonneg_right hLL_ge_1 hL_pos.le
  have h_env_scale : envelopeC θ * (Real.log Q / (Real.pi * Δ)) ≤
      (envelopeC θ + 6 * |envelopeC θ| * (LL / L)) * (Real.log Q / L) := by
    have hpiΔ_eq : Real.pi * Δ = L - 3 * LL := by
      dsimp only [Δ]; field_simp [Real.pi_ne_zero]
    have hdiff : Real.log Q / (Real.pi * Δ) - Real.log Q / L ≤ 6 * (LL / L) * (Real.log Q / L) := by
      rw [hpiΔ_eq]
      have hsub_pos : 0 < L - 3 * LL := by linarith
      have heq : Real.log Q / (L - 3 * LL) - Real.log Q / L =
          (3 * LL * Real.log Q) / (L * (L - 3 * LL)) := by
        field_simp [hL_pos.ne', hsub_pos.ne']; ring
      rw [heq]
      calc (3 * LL * Real.log Q) / (L * (L - 3 * LL))
          ≤ (3 * LL * Real.log Q) / (L * (L / 2)) := by
            gcongr
            exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
        _ = 6 * (LL / L) * (Real.log Q / L) := by
            field_simp [hL_pos.ne']; ring
    have hdiff_nonneg : 0 ≤ Real.log Q / (Real.pi * Δ) - Real.log Q / L := by
      rw [hpiΔ_eq]
      have hsub_pos : 0 < L - 3 * LL := by linarith
      exact sub_nonneg.mpr (div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hsub_pos (by linarith))
    have h1 : envelopeC θ * (Real.log Q / (Real.pi * Δ) - Real.log Q / L) ≤
        |envelopeC θ| * (6 * (LL / L) * (Real.log Q / L)) :=
      calc envelopeC θ * (Real.log Q / (Real.pi * Δ) - Real.log Q / L)
          ≤ |envelopeC θ| * (Real.log Q / (Real.pi * Δ) - Real.log Q / L) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hdiff_nonneg
        _ ≤ |envelopeC θ| * (6 * (LL / L) * (Real.log Q / L)) :=
            mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    linarith
  have h_L2_le : L ^ 2 ≤ Real.log Q := by
    have h3 : L ^ 3 / 6 ≤ Real.exp L := by
      have h_s := Real.sum_le_exp_of_nonneg hL_pos.le 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h_s
      have h3f : (Nat.factorial 3 : ℝ) = 6 := by norm_num
      rw [h3f] at h_s
      linarith [sq_nonneg L]
    have hL6 : 6 ≤ L := by linarith
    have h_exp_L : Real.exp L = Real.log Q := Real.exp_log (by linarith)
    nlinarith
  have h_scale_ge_L : L ≤ Real.log Q / L := by
    rw [le_div_iff₀ hL_pos]
    nlinarith
  have h_one_le_prod : 1 ≤ (LL / L) * (Real.log Q / L) := by
    rw [div_mul_div_comm, one_le_div (mul_pos hL_pos hL_pos)]
    nlinarith
  have h_exp_le_inv_logQ : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log Q := by
    have h_neg : -2 * Real.pi * Δ ≤ -L := by
      have : 2 * Real.pi * Δ = 2 * L - 6 * LL := by dsimp only [Δ]; field_simp [Real.pi_ne_zero]; ring
      linarith
    calc Real.exp (-2 * Real.pi * Δ) ≤ Real.exp (-L) := Real.exp_le_exp.mpr h_neg
      _ = 1 / Real.exp L := by rw [Real.exp_neg, one_div]
      _ = 1 / Real.log Q := by rw [Real.exp_log (by linarith)]
  have h_q1_term : (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0) ≤
      C_sup * Real.log Δ := by
    split_ifs with hq1
    · have hQ_eq : Q = |t| + 2 := by simp [Q, analyticConductor, hq1]
      have ht_ge : Q / 2 ≤ |t| := by linarith
      have ht2_ge : Q ^ 2 / 4 ≤ t ^ 2 := by
        rw [← sq_abs t]; nlinarith
      have hexp_le : Real.exp (Real.pi * Δ) ≤ Real.log Q := by
        have hpiΔ_le : Real.pi * Δ ≤ L := by
          dsimp only [Δ]; rw [mul_div_cancel₀ _ Real.pi_ne_zero]; linarith
        calc Real.exp (Real.pi * Δ) ≤ Real.exp L := Real.exp_le_exp.mpr hpiΔ_le
          _ = Real.log Q := Real.exp_log (by linarith)
      have hlogQ_le : Real.log Q ≤ Q ^ 2 / 4 := by
        have h1 : Real.log Q ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
        nlinarith
      have hdiv_le : Real.exp (Real.pi * Δ) / t ^ 2 ≤ 1 :=
        div_le_one_of_le₀ (hexp_le.trans (hlogQ_le.trans ht2_ge)) (sq_nonneg t)
      calc Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ)
          ≤ 1 * (C_sup * Real.log Δ) := mul_le_mul_of_nonneg_right hdiv_le hM_sup_nonneg
        _ = C_sup * Real.log Δ := one_mul _
    · exact hM_sup_nonneg
  have h_logΔ_le : Real.log Δ ≤ LL := by
    apply Real.log_le_log hΔ_pos
    dsimp only [Δ]
    have : L - 3 * LL ≤ L := by linarith
    calc (L - 3 * LL) / Real.pi ≤ L / Real.pi := div_le_div_of_nonneg_right this Real.pi_pos.le
      _ ≤ L / 1 := div_le_div_of_nonneg_left hL_pos.le zero_lt_one (by linarith [Real.two_le_pi])
      _ = L := div_one L
  have h_gw_err_scale : C₁ * (C_sup * Real.log Δ +
      (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0)) ≤
      (2 * C₁ * C_sup) * (LL / L) * (Real.log Q / L) := by
    calc C₁ * (C_sup * Real.log Δ + _)
        ≤ C₁ * (C_sup * Real.log Δ + C_sup * Real.log Δ) := by gcongr
      _ = (2 * C₁ * C_sup) * Real.log Δ := by ring
      _ ≤ (2 * C₁ * C_sup) * LL := by gcongr
      _ = (2 * C₁ * C_sup) * (LL / L) * L := by field_simp [hL_pos.ne']
      _ ≤ (2 * C₁ * C_sup) * (LL / L) * (Real.log Q / L) := by gcongr
  have h_C0_scale : C₀ ≤ C₀ * (LL / L) * (Real.log Q / L) := by
    calc C₀ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * ((LL / L) * (Real.log Q / L)) := mul_le_mul_of_nonneg_left h_one_le_prod hC₀_pos.le
      _ = C₀ * (LL / L) * (Real.log Q / L) := by ring
  have h_errM_scale : (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) ≤
      (C_err_M / (2 * Real.pi)) * (LL / L) * (Real.log Q / L) := by
    have hlogQ_pos : 0 < Real.log Q := by linarith
    calc (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ))
        ≤ (Real.log Q / (2 * Real.pi)) * (C_err_M * (1 / Real.log Q)) := by gcongr
      _ = C_err_M / (2 * Real.pi) := by field_simp [hlogQ_pos.ne', Real.pi_ne_zero]
      _ = (C_err_M / (2 * Real.pi)) * 1 := (mul_one _).symm
      _ ≤ (C_err_M / (2 * Real.pi)) * ((LL / L) * (Real.log Q / L)) := by
          gcongr
      _ = (C_err_M / (2 * Real.pi)) * (LL / L) * (Real.log Q / L) := by ring
  have h_pps_neg : -primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t ≤
      (4 * C_L1 / Real.pi) * (LL / L) * (Real.log Q / L) :=
    (neg_le_abs _).trans h_pps_scale
  calc polarLogL D q χ t θ
      ≤ (Real.cos θ / 2) * Real.log Q + ∑' n : ℕ, kernelK θ (t - D.zeros q χ n) + C₀ := h_hzs_upper
    _ ≤ (Real.cos θ / 2) * Real.log Q + ∑' n : ℕ, (M_entire (t - D.zeros q χ n)).re + C₀ := by
        linarith
    _ ≤ (Real.cos θ / 2) * Real.log Q +
          ((Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_entire x).re) -
            primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t +
            C₁ * (C_sup * Real.log Δ +
              (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0))) + C₀ := by
        linarith [h_gw_upper]
    _ ≤ (Real.cos θ / 2) * Real.log Q +
          ((-(Real.cos θ / 2) * Real.log Q + envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
            (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ))) -
            primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t +
            C₁ * (C_sup * Real.log Δ +
              (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0))) + C₀ := by
        linarith [h_main_int_bd]
    _ = envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
          (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) +
          (-primePowerSum q χ (fourierHat (fun x : ℝ => M_entire x)) X t) +
          C₁ * (C_sup * Real.log Δ +
            (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0)) + C₀ := by
        ring
    _ ≤ (envelopeC θ + 6 * |envelopeC θ| * (LL / L)) * (Real.log Q / L) +
          (C_err_M / (2 * Real.pi)) * (LL / L) * (Real.log Q / L) +
          (4 * C_L1 / Real.pi) * (LL / L) * (Real.log Q / L) +
          (2 * C₁ * C_sup) * (LL / L) * (Real.log Q / L) +
          C₀ * (LL / L) * (Real.log Q / L) := by
        linarith [h_env_scale, h_errM_scale, h_pps_neg, h_gw_err_scale, h_C0_scale]
    _ ≤ (envelopeC θ + C_err * LL / L) * (Real.log Q / L) := by
        have h_nonneg : 0 ≤ (LL / L) * (Real.log Q / L) := by positivity
        have h_eq1 : (envelopeC θ + 6 * |envelopeC θ| * (LL / L)) * (Real.log Q / L) +
              (C_err_M / (2 * Real.pi)) * (LL / L) * (Real.log Q / L) +
              (4 * C_L1 / Real.pi) * (LL / L) * (Real.log Q / L) +
              (2 * C₁ * C_sup) * (LL / L) * (Real.log Q / L) +
              C₀ * (LL / L) * (Real.log Q / L) =
            envelopeC θ * (Real.log Q / L) +
              (6 * |envelopeC θ| + C_err_M / (2 * Real.pi) + 4 * C_L1 / Real.pi +
                2 * C₁ * C_sup + C₀) * ((LL / L) * (Real.log Q / L)) := by ring
        have h_eq2 : (envelopeC θ + C_err * LL / L) * (Real.log Q / L) =
            envelopeC θ * (Real.log Q / L) + C_err * ((LL / L) * (Real.log Q / L)) := by ring
        rw [h_eq1, h_eq2]
        have h_c_le : 6 * |envelopeC θ| + C_err_M / (2 * Real.pi) + 4 * C_L1 / Real.pi +
            2 * C₁ * C_sup + C₀ ≤ C_err := by
          dsimp only [C_err]; linarith
        linarith [mul_le_mul_of_nonneg_right h_c_le h_nonneg]

/-- **Theorem 1.2 (Part 1)** (Universal convex domain confinement):
For every `ε > 0`, `z(t, χ)` lies in the `ε`-neighborhood of `Ω` for `q(|t| + 2) ≥ q₀(ε)`. -/
theorem convex_domain_confinement (D : LFunctionData) :
    ∀ ε > 0, ∃ Q₀ : ℝ, Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          ∃ w ∈ convexOmega, ‖normalizedLogL D q χ t - w‖ < ε := by
  intro ε hε
  set ε' := min ε 1
  have hε'_pos : 0 < ε' := by positivity
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_le_pi : ε' ≤ 1 := min_le_right _ _
  obtain ⟨Q_S, hQ_S, hS_bd⟩ := ccm_S_bound D (ε' / (4 * Real.pi)) (by positivity)
  obtain ⟨Q_0, C_err0, hQ_0, hC_err0, hdir0⟩ :=
    directional_envelope_bound D 0 (by simp [Real.pi_pos])
  obtain ⟨Q_0', hQ_0', hlll0⟩ := logloglog_div_loglog_lt (ε' / (2 * C_err0)) (by positivity)
  set a : ℝ := (1 / 2) * Real.log (2 * Real.cos (Real.pi / 2 - ε' / 2))
  set b : ℝ := Real.log 2 / 2 + ε' / 2
  set c : ℝ := Real.pi / 4 + ε' / 4
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have hcos_pos : 0 < Real.cos (Real.pi / 2 - ε' / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  let R : Set ℂ := { z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ -c ≤ z.im ∧ z.im ≤ c }
  have hR_compact : IsCompact R := by
    have hprod : IsCompact (Set.Icc a b ×ˢ Set.Icc (-c) c) := isCompact_Icc.prod isCompact_Icc
    have heq : R = Complex.equivRealProdCLM.symm '' (Set.Icc a b ×ˢ Set.Icc (-c) c) := by
      ext z
      simp only [R, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, Prod.exists]
      constructor
      · intro hz
        refine ⟨z.re, z.im, ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩, ?_⟩
        apply Complex.ext <;> simp
      · rintro ⟨x, y, ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, rfl⟩
        simp [hx1, hx2, hy1, hy2]
    rw [heq]
    exact hprod.image Complex.equivRealProdCLM.symm.continuous
  let K : Set ℂ := R ∩ { z : ℂ | ∀ w ∈ convexOmega, ε' / 2 ≤ ‖z - w‖ }
  have hK_closed : IsClosed K := by
    refine IsClosed.inter hR_compact.isClosed ?_
    have : { z : ℂ | ∀ w ∈ convexOmega, ε' / 2 ≤ ‖z - w‖ } =
        ⋂ w ∈ convexOmega, { z : ℂ | ε' / 2 ≤ ‖z - w‖ } := by
      ext z; simp
    rw [this]
    refine isClosed_biInter fun w _ => isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  have hK_compact : IsCompact K := hR_compact.of_isClosed_subset hK_closed Set.inter_subset_left
  let U : ℝ → Set ℂ := fun θ => { z : ℂ | envelopeC θ < z.re * Real.cos θ + z.im * Real.sin θ }
  have hU_open : ∀ θ : ℝ, IsOpen (U θ) := fun θ =>
    isOpen_lt continuous_const ((Complex.continuous_re.mul continuous_const).add
      (Complex.continuous_im.mul continuous_const))
  have hK_cover : K ⊆ ⋃ θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2), U θ := by
    intro z hz
    have hz_not : z ∉ convexOmega := by
      intro hmem
      have := hz.2 z hmem
      simp only [sub_self, norm_zero] at this
      linarith
    by_cases him : |z.im| < Real.pi / 4
    · refine Set.mem_iUnion₂.mpr ⟨2 * z.im, ?_, ?_⟩
      · constructor <;> linarith [(abs_lt.mp him).1, (abs_lt.mp him).2]
      · have hnot_exp : ¬ (Real.exp (2 * z.re) ≤ 2 * Real.cos (2 * z.im)) := by
          intro hexp; exact hz_not ⟨him, hexp⟩
        have hexp_gt : 2 * Real.cos (2 * z.im) < Real.exp (2 * z.re) := not_le.mp hnot_exp
        have hcos2 : 0 < Real.cos (2 * z.im) := by
          apply Real.cos_pos_of_mem_Ioo
          constructor <;> linarith [(abs_lt.mp him).1, (abs_lt.mp him).2]
        have hlog_lt : Real.log (2 * Real.cos (2 * z.im)) < 2 * z.re := by
          rw [← Real.log_exp (2 * z.re)]
          exact Real.log_lt_log (by positivity) hexp_gt
        simp only [U, Set.mem_setOf_eq, envelopeC]
        nlinarith
    · have him_ge : Real.pi / 4 ≤ |z.im| := not_lt.mp him
      set δ := min (Real.pi / 8) (Real.exp (2 * z.re) / 4)
      have hδ_pos : 0 < δ := by positivity
      have hδ_le1 : δ ≤ Real.pi / 8 := min_le_left _ _
      have hδ_le2 : δ ≤ Real.exp (2 * z.re) / 4 := min_le_right _ _
      set sgn : ℝ := if 0 ≤ z.im then 1 else -1
      set θ := sgn * (Real.pi / 2 - δ)
      refine Set.mem_iUnion₂.mpr ⟨θ, ?_, ?_⟩
      · have hpos : 0 < Real.pi / 2 - δ := by linarith [Real.pi_pos]
        have hlt : Real.pi / 2 - δ < Real.pi / 2 := by linarith
        by_cases hs : 0 ≤ z.im
        · simp only [θ, sgn, if_pos hs, one_mul, Set.mem_Ioo]; constructor <;> linarith [Real.pi_pos]
        · simp only [θ, sgn, if_neg hs, neg_one_mul, Set.mem_Ioo]; constructor <;> linarith [Real.pi_pos]
      · simp only [U, Set.mem_setOf_eq, envelopeC]
        have hcos_eq : Real.cos θ = Real.sin δ := by
          by_cases hs : 0 ≤ z.im
          · dsimp only [θ, sgn]; rw [if_pos hs, one_mul, Real.cos_pi_div_two_sub]
          · dsimp only [θ, sgn]; rw [if_neg hs, neg_one_mul, Real.cos_neg, Real.cos_pi_div_two_sub]
        have hsin_eq : z.im * Real.sin θ = |z.im| * Real.cos δ := by
          by_cases hs : 0 ≤ z.im
          · dsimp only [θ, sgn]; rw [if_pos hs, one_mul, Real.sin_pi_div_two_sub, abs_of_nonneg hs]
          · dsimp only [θ, sgn]; rw [if_neg hs, neg_one_mul, Real.sin_neg, Real.sin_pi_div_two_sub, abs_of_neg (not_le.mp hs)]; ring
        have hθsin_eq : θ * Real.sin θ = (Real.pi / 2 - δ) * Real.cos δ := by
          by_cases hs : 0 ≤ z.im
          · dsimp only [θ, sgn]; rw [if_pos hs, one_mul, Real.sin_pi_div_two_sub]
          · dsimp only [θ, sgn]; rw [if_neg hs, neg_one_mul, Real.sin_neg, Real.sin_pi_div_two_sub]; ring
        have hsin_pos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ_pos (by linarith [Real.pi_pos])
        have hcosδ_pos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith [Real.pi_pos])
        have hsin_le : Real.sin δ ≤ δ := Real.sin_le hδ_pos.le
        have hlog_lt : Real.log (2 * Real.sin δ) < 2 * z.re := by
          rw [← Real.log_exp (2 * z.re)]
          apply Real.log_lt_log (by positivity)
          linarith [Real.exp_pos (2 * z.re)]
        rw [hcos_eq, hsin_eq, hθsin_eq]
        have h1 : (1 / 2 : ℝ) * (Real.sin δ * Real.log (2 * Real.sin δ)) < z.re * Real.sin δ := by
          nlinarith
        have h2 : (1 / 2 : ℝ) * ((Real.pi / 2 - δ) * Real.cos δ) < |z.im| * Real.cos δ := by
          nlinarith
        linarith
  obtain ⟨s_set, hs_sub_set, hs_fin, hs_cov⟩ := hK_compact.elim_finite_subcover_image (fun θ _ => hU_open θ) hK_cover
  let s : Finset ℝ := hs_fin.toFinset
  have hs_sub : (s : Set ℝ) ⊆ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
    intro θ hθ
    exact hs_sub_set (hs_fin.mem_toFinset.mp hθ)
  have hs_cov' : K ⊆ ⋃ θ ∈ s, U θ := by
    intro z hz
    obtain ⟨θ, hθ_mem, hzU⟩ := Set.mem_iUnion₂.mp (hs_cov hz)
    exact Set.mem_iUnion₂.mpr ⟨θ, hs_fin.mem_toFinset.mpr hθ_mem, hzU⟩
  -- Now handle s empty vs nonempty
  have h_main : ∃ Q_K ≥ 100, ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
      D.GRH q hq χ hχ → ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q_K →
      normalizedLogL D q χ t ∉ K := by
    by_cases hs_ne : s.Nonempty
    · have hK_ne : K.Nonempty → ∃ δ₀ > 0, ∀ z ∈ K,
          ∃ θ ∈ s, envelopeC θ + δ₀ ≤ z.re * Real.cos θ + z.im * Real.sin θ := by
        intro hKne
        let g : ℂ → ℝ := fun z => s.sup' hs_ne (fun θ => z.re * Real.cos θ + z.im * Real.sin θ - envelopeC θ)
        have hg_cont : Continuous g := by
          have h_ind : ∀ (t : Finset ℝ) (ht : t.Nonempty),
              Continuous (fun z : ℂ => t.sup' ht (fun θ => z.re * Real.cos θ + z.im * Real.sin θ - envelopeC θ)) := by
            intro t ht
            induction t using Finset.Nonempty.cons_induction with
            | singleton a =>
              simp only [Finset.sup'_singleton]
              fun_prop
            | cons a t ha ht' ih =>
              simp only [Finset.sup'_cons]
              exact Continuous.max (by fun_prop) ih
          exact h_ind s hs_ne
        obtain ⟨z_min, hz_min, hz_isMin⟩ := hK_compact.exists_isMinOn hKne hg_cont.continuousOn
        have hg_pos : 0 < g z_min := by
          have hmem := hs_cov' hz_min
          simp only [Set.mem_iUnion, exists_prop] at hmem
          obtain ⟨θ, hθs, hθU⟩ := hmem
          have hlt : 0 < z_min.re * Real.cos θ + z_min.im * Real.sin θ - envelopeC θ := by
            simpa [U] using hθU
          exact hlt.trans_le (Finset.le_sup' (fun θ => z_min.re * Real.cos θ + z_min.im * Real.sin θ - envelopeC θ) hθs)
        refine ⟨g z_min, hg_pos, fun z hz => ?_⟩
        have hle := hz_isMin hz
        obtain ⟨θ, hθs, hθeq⟩ := Finset.exists_mem_eq_sup' hs_ne
          (fun θ => z.re * Real.cos θ + z.im * Real.sin θ - envelopeC θ)
        refine ⟨θ, hθs, ?_⟩
        dsimp only [g, Set.mem_setOf_eq] at hle
        linarith
      by_cases hKne : K.Nonempty
      · obtain ⟨δ₀, hδ₀, hK_gap⟩ := hK_ne hKne
        have h_each : ∀ θ ∈ s, ∃ Q_θ ≥ 100,
            ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
              D.GRH q hq χ hχ → ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q_θ →
              (normalizedLogL D q χ t).re * Real.cos θ + (normalizedLogL D q χ t).im * Real.sin θ <
                envelopeC θ + δ₀ := by
          intro θ hθs
          have hθ_mem := hs_sub hθs
          have hθ_abs : |θ| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [hθ_mem.1], hθ_mem.2⟩
          obtain ⟨Q_θ, C_θ, hQ_θ, hC_θ, hdir_θ⟩ := directional_envelope_bound D θ hθ_abs
          obtain ⟨Q_θ', hQ_θ', hlll_θ⟩ := logloglog_div_loglog_lt (δ₀ / C_θ) (by positivity)
          refine ⟨max Q_θ Q_θ', le_trans hQ_θ (le_max_left _ _),
            fun q hq χ hχ hGRH t ht hcond => ?_⟩
          have h100 : 100 ≤ analyticConductor q t := le_trans hQ_θ (le_trans (le_max_left _ _) hcond)
          have hscale := scale_pos_of_ge_100 h100
          have hbound := hdir_θ q hq χ hχ hGRH t ht (le_trans (le_max_left _ _) hcond)
          have hlll := (hlll_θ (analyticConductor q t) (le_trans (le_max_right _ _) hcond)).2
          have hproj : (normalizedLogL D q χ t).re * Real.cos θ +
              (normalizedLogL D q χ t).im * Real.sin θ =
              polarLogL D q χ t θ / (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
            simp only [normalizedLogL, polarLogL]
            ring
          rw [hproj, div_lt_iff₀ hscale]
          have hC_lt : C_θ * Real.log (Real.log (Real.log (analyticConductor q t))) /
              Real.log (Real.log (analyticConductor q t)) < δ₀ := by
            rw [mul_div_assoc]
            calc C_θ * (Real.log (Real.log (Real.log (analyticConductor q t))) /
                  Real.log (Real.log (analyticConductor q t)))
                < C_θ * (δ₀ / C_θ) := mul_lt_mul_of_pos_left hlll hC_θ
              _ = δ₀ := by field_simp [hC_θ.ne']
          exact hbound.trans_lt (mul_lt_mul_of_pos_right (by linarith) hscale)
        choose Q_fn hQ_fn using h_each
        let Q_max : ℝ := s.attach.sup' (by simpa using hs_ne) (fun ⟨θ, hθ⟩ => Q_fn θ hθ)
        refine ⟨max 100 Q_max, le_max_left _ _, fun q hq χ hχ hGRH t ht hcond hzK => ?_⟩
        obtain ⟨θ, hθs, hgap⟩ := hK_gap _ hzK
        have hQ_le : Q_fn θ hθs ≤ Q_max :=
          Finset.le_sup' (fun ⟨θ', hθ'⟩ => Q_fn θ' hθ') (Finset.mem_attach s ⟨θ, hθs⟩)
        have hlt := (hQ_fn θ hθs).2 q hq χ hχ hGRH t ht (le_trans hQ_le (le_trans (le_max_right _ _) hcond))
        linarith
      · refine ⟨100, le_rfl, fun q hq χ hχ hGRH t ht hcond hzK => hKne ⟨_, hzK⟩⟩
    · refine ⟨100, le_rfl, fun q hq χ hχ hGRH t ht hcond hzK => ?_⟩
      have hmem := hs_cov' hzK
      simp only [Set.mem_iUnion, exists_prop] at hmem
      obtain ⟨θ, hθs, _⟩ := hmem
      exact hs_ne ⟨θ, hθs⟩
  obtain ⟨Q_K, hQ_K, hnotK⟩ := h_main
  refine ⟨max (max Q_S Q_K) (max Q_0 Q_0'),
    le_trans hQ_0 (le_trans (le_max_left _ _) (le_max_right _ _)),
    fun q hq χ hχ hGRH t ht hcond => ?_⟩
  have h100 : 100 ≤ analyticConductor q t :=
    le_trans hQ_0 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hcond))
  have hscale := scale_pos_of_ge_100 h100
  have hS_im : |(normalizedLogL D q χ t).im| ≤ c := by
    have hS := hS_bd q hq χ hχ hGRH t ht (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hcond))
    simp only [normalizedLogL]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hscale, div_le_iff₀ hscale]
    calc Real.pi * |D.S_val q χ t|
        ≤ Real.pi * ((1 / 4 + ε' / (4 * Real.pi)) *
            (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t)))) := by
          gcongr
      _ = c * (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
          dsimp only [c]; field_simp [Real.pi_ne_zero]
  have h_re_le : (normalizedLogL D q χ t).re ≤ b := by
    have h0 := hdir0 q hq χ hχ hGRH t ht (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hcond))
    have hlll := (hlll0 (analyticConductor q t) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hcond))).2
    have hC0 : envelopeC 0 = Real.log 2 / 2 := by
      simp [envelopeC, Real.cos_zero, Real.sin_zero]; ring
    have hpol : polarLogL D q χ t 0 = D.logAbsL q χ t := by
      simp [polarLogL, Real.cos_zero, Real.sin_zero]
    have hC_lt : C_err0 * Real.log (Real.log (Real.log (analyticConductor q t))) /
        Real.log (Real.log (analyticConductor q t)) < ε' / 2 := by
      rw [mul_div_assoc]
      calc C_err0 * (Real.log (Real.log (Real.log (analyticConductor q t))) /
            Real.log (Real.log (analyticConductor q t)))
          < C_err0 * (ε' / (2 * C_err0)) := mul_lt_mul_of_pos_left hlll hC_err0
        _ = ε' / 2 := by field_simp [hC_err0.ne']
    simp only [normalizedLogL]
    rw [div_le_iff₀ hscale]
    rw [hpol] at h0
    rw [hC0] at h0
    dsimp only [b]
    exact h0.trans (mul_le_mul_of_nonneg_right (by linarith) hscale.le)
  by_cases ha : a ≤ (normalizedLogL D q χ t).re
  · have hzR : normalizedLogL D q χ t ∈ R := ⟨ha, h_re_le, (abs_le.mp hS_im).1, (abs_le.mp hS_im).2⟩
    have hz_notK := hnotK q hq χ hχ hGRH t ht (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hcond))
    have hnot_all : ¬ ∀ w ∈ convexOmega, ε' / 2 ≤ ‖normalizedLogL D q χ t - w‖ :=
      fun hall => hz_notK ⟨hzR, hall⟩
    push Not at hnot_all
    obtain ⟨w, hw, hzw⟩ := hnot_all
    exact ⟨w, hw, hzw.trans_le (by linarith)⟩
  · have ha_lt : (normalizedLogL D q χ t).re < a := not_le.mp ha
    set z := normalizedLogL D q χ t
    by_cases hy : |z.im| ≤ Real.pi / 4 - ε' / 4
    · refine ⟨z, ⟨?_, ?_⟩, by simp; exact hε⟩
      · linarith
      · have hcos_ge : Real.cos (Real.pi / 2 - ε' / 2) ≤ Real.cos (2 * z.im) := by
          rw [← Real.cos_abs (2 * z.im)]
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          · positivity
          · linarith [abs_nonneg z.im, Real.pi_pos]
          · rw [abs_mul, abs_of_pos two_pos]; linarith
        have hexp_lt : Real.exp (2 * z.re) ≤ 2 * Real.cos (Real.pi / 2 - ε' / 2) := by
          have : 2 * z.re ≤ Real.log (2 * Real.cos (Real.pi / 2 - ε' / 2)) := by
            dsimp only [a] at ha_lt; linarith
          calc Real.exp (2 * z.re) ≤ Real.exp (Real.log (2 * Real.cos (Real.pi / 2 - ε' / 2))) := by gcongr
            _ = 2 * Real.cos (Real.pi / 2 - ε' / 2) := Real.exp_log (by positivity)
        linarith
    · set y₀ : ℝ := if 0 ≤ z.im then Real.pi / 4 - ε' / 4 else -(Real.pi / 4 - ε' / 4)
      let w : ℂ := ⟨z.re, y₀⟩
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · have hy0 : |y₀| = Real.pi / 4 - ε' / 4 := by
          by_cases h0 : 0 ≤ z.im
          · dsimp only [y₀]; rw [if_pos h0, abs_of_nonneg (by linarith)]
          · dsimp only [y₀]; rw [if_neg h0, abs_neg, abs_of_nonneg (by linarith)]
        rw [hy0]; linarith
      · have hcos_eq : Real.cos (2 * y₀) = Real.cos (Real.pi / 2 - ε' / 2) := by
          by_cases h0 : 0 ≤ z.im
          · dsimp only [y₀]; rw [if_pos h0]; ring_nf
          · dsimp only [y₀]; rw [if_neg h0, mul_neg, Real.cos_neg]; ring_nf
        have hexp_lt : Real.exp (2 * z.re) ≤ 2 * Real.cos (Real.pi / 2 - ε' / 2) := by
          have : 2 * z.re ≤ Real.log (2 * Real.cos (Real.pi / 2 - ε' / 2)) := by
            dsimp only [a] at ha_lt; linarith
          calc Real.exp (2 * z.re) ≤ Real.exp (Real.log (2 * Real.cos (Real.pi / 2 - ε' / 2))) := by gcongr
            _ = 2 * Real.cos (Real.pi / 2 - ε' / 2) := Real.exp_log (by positivity)
        change Real.exp (2 * z.re) ≤ 2 * Real.cos (2 * y₀)
        linarith
      · have him_lt : |z.im - y₀| ≤ ε' / 2 := by
          have hy_gt : Real.pi / 4 - ε' / 4 < |z.im| := not_le.mp hy
          by_cases h0 : 0 ≤ z.im
          · simp only [y₀, if_pos h0]
            rw [abs_of_nonneg h0] at hy_gt
            have him_le : z.im ≤ Real.pi / 4 + ε' / 4 := (abs_le.mp hS_im).2
            rw [abs_le]; constructor <;> linarith
          · simp only [y₀, if_neg h0]
            rw [abs_of_neg (not_le.mp h0)] at hy_gt
            have him_ge : -(Real.pi / 4 + ε' / 4) ≤ z.im := (abs_le.mp hS_im).1
            rw [abs_le]; constructor <;> linarith
        have hdiff : z - w = ((z.im - y₀ : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [w]
        rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        linarith

/-- **Theorem 1.2 (Part 2)** (Modulus–argument tradeoff):
If `log|L(1/2 + it, χ)| ≥ (α - δ) log q / log log q` with `α ≤ (log 2)/2`,
then `|S(t, χ)| ≤ (arccos(e^{2α}/2)/(2π) + o(1)) log q / log log q`. -/
theorem modulus_argument_tradeoff (D : LFunctionData) (α : ℝ) (hα : α ≤ Real.log 2 / 2) :
    ∀ ε > 0, ∃ (δ Q₀ : ℝ), δ > 0 ∧ Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ (α - δ) * (Real.log (analyticConductor q t) /
            Real.log (Real.log (analyticConductor q t))) →
          |D.S_val q χ t| ≤
            (Real.arccos (Real.exp (2 * α) / 2) / (2 * Real.pi) + ε) *
              (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  intro ε hε
  let f : ℝ → ℝ := fun r => Real.arccos (min 1 (Real.exp (2 * r) / 2))
  have hf_cont : Continuous f := by
    apply Continuous.comp Real.continuous_arccos
    exact continuous_const.min ((Real.continuous_exp.comp (continuous_const.mul continuous_id')).div_const 2)
  have hf_at : f α = Real.arccos (Real.exp (2 * α) / 2) := by
    have hle : Real.exp (2 * α) / 2 ≤ 1 := by
      have : 2 * α ≤ Real.log 2 := by linarith
      calc Real.exp (2 * α) / 2 ≤ Real.exp (Real.log 2) / 2 := by gcongr
        _ = 1 := by rw [Real.exp_log (by norm_num)]; norm_num
    simp [f, min_eq_right hle]
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp hf_cont.continuousAt (Real.pi * ε) (by positivity)
  set ε₁ := min (η / 3) (Real.pi * ε / 2)
  have hε₁_pos : 0 < ε₁ := by positivity
  obtain ⟨Q₀, hQ₀, hconf⟩ := convex_domain_confinement D ε₁ hε₁_pos
  refine ⟨η / 3, Q₀, by positivity, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hscale := scale_pos_of_ge_100 (le_trans hQ₀ hcond)
  set scale := Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))
  obtain ⟨w, hw, hzw⟩ := hconf q hq χ hχ hGRH t ht hcond
  have hre : |(normalizedLogL D q χ t - w).re| < ε₁ :=
    (Complex.abs_re_le_norm _).trans_lt hzw
  have him : |(normalizedLogL D q χ t - w).im| < ε₁ :=
    (Complex.abs_im_le_norm _).trans_lt hzw
  have hz_re : (normalizedLogL D q χ t).re ≥ α - η / 3 := by
    simp only [normalizedLogL]
    rw [ge_iff_le, le_div_iff₀ hscale]
    exact hlog
  have hw_re : w.re > α - η / 3 - ε₁ := by
    have : (normalizedLogL D q χ t - w).re = (normalizedLogL D q χ t).re - w.re := rfl
    linarith [(abs_lt.mp hre).2]
  have hw_im_bd : |w.im| < Real.pi / 4 := hw.1
  have hw_exp : Real.exp (2 * w.re) ≤ 2 * Real.cos (2 * w.im) := hw.2
  have hcos_ge : min 1 (Real.exp (2 * (α - η / 3 - ε₁)) / 2) ≤ Real.cos (2 * w.im) := by
    refine le_trans (min_le_right _ _) ?_
    have : Real.exp (2 * (α - η / 3 - ε₁)) ≤ Real.exp (2 * w.re) := by gcongr
    linarith
  have h2wim_nonneg : 0 ≤ 2 * |w.im| := by positivity
  have h2wim_le : 2 * |w.im| ≤ Real.pi := by linarith [abs_nonneg w.im, Real.pi_pos]
  have harccos_eq : 2 * |w.im| = Real.arccos (Real.cos (2 * w.im)) := by
    rw [← Real.cos_abs (2 * w.im), show |2 * w.im| = 2 * |w.im| by rw [abs_mul, abs_of_pos two_pos]]
    exact (Real.arccos_cos h2wim_nonneg h2wim_le).symm
  have harccos_le : Real.arccos (Real.cos (2 * w.im)) ≤ f (α - η / 3 - ε₁) :=
    Real.arccos_le_arccos hcos_ge
  have hdist : dist (α - η / 3 - ε₁) α < η := by
    rw [Real.dist_eq, show α - η / 3 - ε₁ - α = -(η / 3 + ε₁) by ring, abs_neg,
      abs_of_pos (by positivity)]
    have : ε₁ ≤ η / 3 := min_le_left _ _
    linarith
  have hf_lt : f (α - η / 3 - ε₁) < Real.arccos (Real.exp (2 * α) / 2) + Real.pi * ε := by
    have h1 := hcont hdist
    rw [Real.dist_eq, hf_at] at h1
    linarith [(abs_lt.mp h1).2]
  have hw_im_le : |w.im| ≤ Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε / 2 := by
    linarith
  have hz_im_le : |(normalizedLogL D q χ t).im| ≤
      Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε := by
    have him' : |(normalizedLogL D q χ t).im - w.im| < ε₁ := him
    have htri : |(normalizedLogL D q χ t).im| ≤ |w.im| + |(normalizedLogL D q χ t).im - w.im| := by
      calc |(normalizedLogL D q χ t).im|
          = |w.im + ((normalizedLogL D q χ t).im - w.im)| := by ring_nf
        _ ≤ |w.im| + |(normalizedLogL D q χ t).im - w.im| := abs_add_le _ _
    have hε₁_le : ε₁ ≤ Real.pi * ε / 2 := min_le_right _ _
    linarith
  have hS_eq : |D.S_val q χ t| = |(normalizedLogL D q χ t).im| * scale / Real.pi := by
    simp only [normalizedLogL]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hscale]
    field_simp [Real.pi_ne_zero]
  rw [hS_eq]
  calc |(normalizedLogL D q χ t).im| * scale / Real.pi
      ≤ (Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε) * scale / Real.pi := by
        gcongr
    _ = (Real.arccos (Real.exp (2 * α) / 2) / (2 * Real.pi) + ε) * scale := by
        field_simp [Real.pi_ne_zero]

/-- **Corollary 1.3(i)**: Whenever `|L(1/2 + it, χ)| ≥ 1`, `|S(t, χ)| ≤ (1/6 + o(1)) log q / log log q`. -/
theorem corollary_1_3_i (D : LFunctionData) :
    ∀ ε > 0, ∃ Q₀ : ℝ, Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ 0 →
          |D.S_val q χ t| ≤ (1 / 6 + ε) *
            (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  intro ε hε
  have hα : (0 : ℝ) ≤ Real.log 2 / 2 := by positivity
  obtain ⟨δ, Q₀, hδ, hQ₀, hmain⟩ := modulus_argument_tradeoff D 0 hα ε hε
  refine ⟨Q₀, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hscale := (scale_pos_of_ge_100 (le_trans hQ₀ hcond)).le
  have hlog' : D.logAbsL q χ t ≥ (0 - δ) * (Real.log (analyticConductor q t) /
      Real.log (Real.log (analyticConductor q t))) := by
    have : (0 - δ) * (Real.log (analyticConductor q t) /
        Real.log (Real.log (analyticConductor q t))) ≤ 0 := by nlinarith
    linarith
  have hres := hmain q hq χ hχ hGRH t ht hcond hlog'
  have harc : Real.arccos (Real.exp (2 * 0) / 2) / (2 * Real.pi) = 1 / 6 := by
    rw [mul_zero, Real.exp_zero]
    have hcos : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← hcos, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
    field_simp [Real.pi_ne_zero]
    norm_num
  rwa [harc] at hres

/-- **Corollary 1.3(ii)**: Whenever `log|L(1/2 + it, χ)| ≥ ((log 2)/2 - δ) log q / log log q`,
we have `|S(t, χ)| ≤ ε log q / log log q`. -/
theorem corollary_1_3_ii (D : LFunctionData) :
    ∀ ε > 0, ∃ (δ Q₀ : ℝ), δ > 0 ∧ Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ (Real.log 2 / 2 - δ) * (Real.log (analyticConductor q t) /
            Real.log (Real.log (analyticConductor q t))) →
          |D.S_val q χ t| ≤ ε *
            (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  intro ε hε
  obtain ⟨δ, Q₀, hδ, hQ₀, hmain⟩ := modulus_argument_tradeoff D (Real.log 2 / 2) le_rfl ε hε
  refine ⟨δ, Q₀, hδ, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hres := hmain q hq χ hχ hGRH t ht hcond hlog
  have harc : Real.arccos (Real.exp (2 * (Real.log 2 / 2)) / 2) / (2 * Real.pi) = 0 := by
    have h1 : 2 * (Real.log 2 / 2) = Real.log 2 := by ring
    rw [h1, Real.exp_log (by norm_num), div_self (by norm_num), Real.arccos_one, zero_div]
  rwa [harc, zero_add] at hres

/-- **Corollary 1.3(iii)**: In the `q`-aspect at `s = 1/2`, normalized `log L(1/2, χ)` lies in the
`ε`-neighborhood of `Ω` for `q ≥ q₀(ε)`. -/
lemma complex_norm_le_abs_re_add_abs_im (u : ℂ) : ‖u‖ ≤ |u.re| + |u.im| := by
  calc ‖u‖ = ‖(u.re : ℂ) + (u.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(u.re : ℂ)‖ + ‖(u.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |u.re| + |u.im| := by simp

theorem corollary_1_3_iii (D : LFunctionData) :
    ∀ ε > 0, ∃ q₀ : ℕ, q₀ ≥ 10 ∧
      ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq1 χ hχ →
        D.nonvanishing q χ 0 →
        let scale := Real.log (q : ℝ) / Real.log (Real.log (q : ℝ))
        ∃ w ∈ convexOmega, ‖(⟨D.logAbsL q χ 0 / scale, (Real.pi * D.S_val q χ 0) / scale⟩ : ℂ) - w‖ < ε := by
  intro ε hε
  set ε₁ := min (ε / 10) (1 / 2)
  have hε₁_pos : 0 < ε₁ := by positivity
  have hε₁_le1 : ε₁ ≤ ε / 10 := min_le_left _ _
  have hε₁_le2 : ε₁ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨Q₀, hQ₀, hconf⟩ := convex_domain_confinement D ε₁ hε₁_pos
  set q_exp := Nat.ceil (Real.exp (Real.log 2 / ε₁)) + 100
  refine ⟨max (Nat.ceil Q₀) q_exp, le_trans (by dsimp only [q_exp]; omega) (le_max_right _ _),
    fun q hq1 hq χ hχ hGRH hnv => ?_⟩
  have hq_ge_Q₀ : Q₀ ≤ (q : ℝ) :=
    (Nat.le_ceil Q₀).trans (by exact_mod_cast le_trans (le_max_left _ _) hq)
  have hq_ge_100 : (100 : ℝ) ≤ (q : ℝ) := by
    have : 100 ≤ q := le_trans (by omega) (le_trans (le_max_right _ _) hq)
    exact_mod_cast this
  have hq_ge_exp : Real.exp (Real.log 2 / ε₁) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.log 2 / ε₁)) ≤ q :=
      le_trans (by omega) (le_trans (le_max_right _ _) hq)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hcond_eq : analyticConductor q 0 = 2 * (q : ℝ) := by
    simp [analyticConductor]
    ring
  have hcond_ge : analyticConductor q 0 ≥ Q₀ := by linarith
  have hcond_100 : (100 : ℝ) ≤ analyticConductor q 0 := le_trans hQ₀ hcond_ge
  obtain ⟨w, hw, hzw⟩ := hconf q hq1 χ hχ hGRH 0 hnv hcond_ge
  set scale₂ := Real.log (analyticConductor q 0) / Real.log (Real.log (analyticConductor q 0))
  set scale₁ := Real.log (q : ℝ) / Real.log (Real.log (q : ℝ))
  have hscale₁_pos : 0 < scale₁ := scale_pos_of_ge_100 hq_ge_100
  have hscale₂_pos : 0 < scale₂ := scale_pos_of_ge_100 hcond_100
  set c := scale₂ / scale₁
  have hc_ge_one : 1 ≤ c := by
    rw [le_div_iff₀ hscale₁_pos, one_mul]
    have hu : Real.exp 1 ≤ Real.log (q : ℝ) := by
      have h100 : Real.exp (Real.exp 1) ≤ 100 := by
        have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        exact (calc Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he
          _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          _ ≤ 3 * 3 * 3 := by gcongr
          _ ≤ 100 := by norm_num).le
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) (h100.trans hq_ge_100)
    have hv : Real.log (q : ℝ) ≤ Real.log (analyticConductor q 0) :=
      Real.log_le_log (by linarith) (by linarith)
    have hmono : MonotoneOn (fun t : ℝ => t / Real.log t) (Set.Ici (Real.exp 1)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici (Real.exp 1))
      · refine continuousOn_id.div (Real.continuousOn_log.mono fun t ht => ?_) ?_
        · 
          have : Real.exp 1 ≤ t := ht
          exact Set.mem_compl_singleton_iff.mpr (by linarith [Real.exp_pos 1])
        · intro t ht
          have : Real.exp 1 ≤ t := ht
          have : 1 < t := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) this
          exact (Real.log_pos this).ne'
      · intro t ht
        have ht_ge : Real.exp 1 < t := by
          simpa [interior_Ici] using ht
        have ht_pos : 0 < t := lt_trans (Real.exp_pos 1) ht_ge
        have hlog_gt : 1 < Real.log t := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1) ht_ge
        have hlog_ne : Real.log t ≠ 0 := by linarith
        exact ((differentiableAt_id).div (Real.differentiableAt_log ht_pos.ne') hlog_ne).differentiableWithinAt
      · intro t ht
        have ht_ge : Real.exp 1 < t := by
          simpa [interior_Ici] using ht
        have ht_pos : 0 < t := lt_trans (Real.exp_pos 1) ht_ge
        have hlog_gt : 1 < Real.log t := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1) ht_ge
        have hlog_ne : Real.log t ≠ 0 := by linarith
        have hder : HasDerivAt (fun s : ℝ => s / Real.log s)
            ((1 * Real.log t - t * t⁻¹) / (Real.log t) ^ 2) t :=
          (hasDerivAt_id t).div (Real.hasDerivAt_log ht_pos.ne') hlog_ne
        rw [hder.deriv]
        have hnum : 0 ≤ 1 * Real.log t - t * t⁻¹ := by
          rw [one_mul, mul_inv_cancel₀ ht_pos.ne']; linarith
        exact div_nonneg hnum (sq_nonneg _)
    exact hmono hu (hu.trans hv) hv
  have hc_le : c ≤ 1 + ε₁ := by
    have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
    have hloglogq_pos : 0 < Real.log (Real.log (q : ℝ)) := by
      apply Real.log_pos
      have : Real.exp 1 ≤ Real.log (q : ℝ) := by
        have h100 : Real.exp (Real.exp 1) ≤ 100 := by
          have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
          exact (calc Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he
            _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            _ ≤ 3 * 3 * 3 := by gcongr
            _ ≤ 100 := by norm_num).le
        rw [← Real.log_exp (Real.exp 1)]
        exact Real.log_le_log (Real.exp_pos _) (h100.trans hq_ge_100)
      linarith [Real.one_lt_exp_iff.mpr one_pos]
    have hloglog_le : Real.log (Real.log (q : ℝ)) ≤ Real.log (Real.log (analyticConductor q 0)) :=
      Real.log_le_log hlogq_pos (Real.log_le_log (by linarith) (by linarith))
    have hdiv_le : Real.log (Real.log (q : ℝ)) / Real.log (Real.log (analyticConductor q 0)) ≤ 1 :=
      div_le_one_of_le₀ hloglog_le (hloglogq_pos.le.trans hloglog_le)
    have hlog2_le : Real.log 2 / Real.log (q : ℝ) ≤ ε₁ := by
      have h1 : Real.log 2 / ε₁ ≤ Real.log (q : ℝ) := by
        rw [← Real.log_exp (Real.log 2 / ε₁)]
        exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
      rw [div_le_iff₀ hlogq_pos]
      rw [div_le_iff₀ hε₁_pos] at h1
      linarith
    have hc_eq : c = (Real.log (analyticConductor q 0) / Real.log (q : ℝ)) *
        (Real.log (Real.log (q : ℝ)) / Real.log (Real.log (analyticConductor q 0))) := by
      dsimp only [c, scale₂, scale₁]
      field_simp
    rw [hc_eq]
    calc (Real.log (analyticConductor q 0) / Real.log (q : ℝ)) *
          (Real.log (Real.log (q : ℝ)) / Real.log (Real.log (analyticConductor q 0)))
        ≤ (Real.log (analyticConductor q 0) / Real.log (q : ℝ)) * 1 := by
          gcongr
          exact div_nonneg (Real.log_nonneg (by linarith)) hlogq_pos.le
      _ = (Real.log (q : ℝ) + Real.log 2) / Real.log (q : ℝ) := by
          rw [mul_one, hcond_eq, Real.log_mul two_ne_zero (by linarith), add_comm]
      _ = 1 + Real.log 2 / Real.log (q : ℝ) := by
          rw [add_div, div_self hlogq_pos.ne']
      _ ≤ 1 + ε₁ := by linarith
  set zq : ℂ := ⟨D.logAbsL q χ 0 / scale₁, (Real.pi * D.S_val q χ 0) / scale₁⟩
  set z₂ := normalizedLogL D q χ 0
  have hlog_q_ne : Real.log (q : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hlog_c_ne : Real.log (analyticConductor q 0) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hloglog_q_ne : Real.log (Real.log (q : ℝ)) ≠ 0 := by
    have : 0 < Real.log (Real.log (q : ℝ)) := by
      dsimp only [scale₁] at hscale₁_pos
      exact (div_pos_iff.mp hscale₁_pos).elim (fun h => h.2) (fun h => by linarith [Real.log_pos (by linarith : (1 : ℝ) < q)])
    exact this.ne'
  have hloglog_c_ne : Real.log (Real.log (analyticConductor q 0)) ≠ 0 := by
    have : 0 < Real.log (Real.log (analyticConductor q 0)) := by
      dsimp only [scale₂] at hscale₂_pos
      exact (div_pos_iff.mp hscale₂_pos).elim (fun h => h.2) (fun h => by linarith [Real.log_pos (by linarith : (1 : ℝ) < analyticConductor q 0)])
    exact this.ne'
  have hzq_re : zq.re = c * z₂.re := by
    dsimp only [zq, z₂, normalizedLogL, c, scale₂, scale₁]
    field_simp [hlog_q_ne, hlog_c_ne, hloglog_q_ne, hloglog_c_ne]
  have hzq_im : zq.im = c * z₂.im := by
    dsimp only [zq, z₂, normalizedLogL, c, scale₂, scale₁]
    field_simp [hlog_q_ne, hlog_c_ne, hloglog_q_ne, hloglog_c_ne]
  have hre_bd : |z₂.re - w.re| < ε₁ := (Complex.abs_re_le_norm _).trans_lt hzw
  have him_bd : |z₂.im - w.im| < ε₁ := (Complex.abs_im_le_norm _).trans_lt hzw
  have hpi_le : Real.pi < 4 := Real.pi_lt_four
  have hc_pos : 0 < c := by linarith
  have hc1_nonneg : 0 ≤ c - 1 := by linarith
  by_cases hw_nonpos : w.re ≤ 0
  · let w' : ℂ := ⟨c * w.re, w.im⟩
    refine ⟨w', ⟨hw.1, ?_⟩, ?_⟩
    · have : c * w.re ≤ w.re := by nlinarith
      calc Real.exp (2 * w'.re) = Real.exp (2 * (c * w.re)) := rfl
        _ ≤ Real.exp (2 * w.re) := by gcongr
        _ ≤ 2 * Real.cos (2 * w.im) := hw.2
    · have hnorm_le : ‖zq - w'‖ ≤ |(zq - w').re| + |(zq - w').im| := complex_norm_le_abs_re_add_abs_im _
      have hd_re : |(zq - w').re| ≤ (1 + ε₁) * ε₁ := by
        have : (zq - w').re = c * (z₂.re - w.re) := by simp [w', hzq_re]; ring
        rw [this, abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul hc_le hre_bd.le (abs_nonneg _) (by linarith)
      have hd_im : |(zq - w').im| ≤ (1 + ε₁) * ε₁ + ε₁ * (Real.pi / 4) := by
        have : (zq - w').im = c * (z₂.im - w.im) + (c - 1) * w.im := by simp [w', hzq_im]; ring
        rw [this]
        have h1 : |c * (z₂.im - w.im)| ≤ (1 + ε₁) * ε₁ := by
          rw [abs_mul, abs_of_pos hc_pos]
          exact mul_le_mul hc_le him_bd.le (abs_nonneg _) (by linarith)
        have h2 : |(c - 1) * w.im| ≤ ε₁ * (Real.pi / 4) := by
          rw [abs_mul, abs_of_nonneg hc1_nonneg]
          exact mul_le_mul (by linarith) hw.1.le (abs_nonneg _) (by linarith)
        exact (abs_add_le _ _).trans (add_le_add h1 h2)
      nlinarith
  · have hw_pos : 0 < w.re := not_le.mp hw_nonpos
    have hw_le : w.re ≤ 1 := by
      have hexp : Real.exp (2 * w.re) ≤ 2 := by
        calc Real.exp (2 * w.re) ≤ 2 * Real.cos (2 * w.im) := hw.2
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by norm_num)
          _ = 2 := by norm_num
      have h2w : 2 * w.re ≤ Real.log 2 := by
        rw [← Real.log_exp (2 * w.re)]
        exact Real.log_le_log (Real.exp_pos _) hexp
      have hlog2_lt : Real.log 2 < 2 := (Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)).trans_le (by norm_num)
      linarith
    refine ⟨w, hw, ?_⟩
    have hnorm_le : ‖zq - w‖ ≤ |(zq - w).re| + |(zq - w).im| := complex_norm_le_abs_re_add_abs_im _
    have hd_re : |(zq - w).re| ≤ (1 + ε₁) * ε₁ + ε₁ := by
      have : (zq - w).re = c * (z₂.re - w.re) + (c - 1) * w.re := by simp [hzq_re]; ring
      rw [this]
      have h1 : |c * (z₂.re - w.re)| ≤ (1 + ε₁) * ε₁ := by
        rw [abs_mul, abs_of_pos hc_pos]
        exact mul_le_mul hc_le hre_bd.le (abs_nonneg _) (by linarith)
      have h2 : |(c - 1) * w.re| ≤ ε₁ := by
        rw [abs_mul, abs_of_nonneg hc1_nonneg, abs_of_pos hw_pos]
        calc (c - 1) * w.re ≤ ε₁ * 1 := mul_le_mul (by linarith) hw_le hw_pos.le (by linarith)
          _ = ε₁ := mul_one _
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    have hd_im : |(zq - w).im| ≤ (1 + ε₁) * ε₁ + ε₁ * (Real.pi / 4) := by
      have : (zq - w).im = c * (z₂.im - w.im) + (c - 1) * w.im := by simp [hzq_im]; ring
      rw [this]
      have h1 : |c * (z₂.im - w.im)| ≤ (1 + ε₁) * ε₁ := by
        rw [abs_mul, abs_of_pos hc_pos]
        exact mul_le_mul hc_le him_bd.le (abs_nonneg _) (by linarith)
      have h2 : |(c - 1) * w.im| ≤ ε₁ * (Real.pi / 4) := by
        rw [abs_mul, abs_of_nonneg hc1_nonneg]
        exact mul_le_mul (by linarith) hw.1.le (abs_nonneg _) (by linarith)
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    nlinarith

end PolarEvaluation