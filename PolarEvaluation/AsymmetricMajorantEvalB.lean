import PolarEvaluation.AsymmetricMajorantDiffB

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

set_option maxHeartbeats 800000 in
lemma tsum_rescaledF_eval (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₄ C_eval : ℝ), Δ₄ ≥ 1 ∧ C_eval > 0 ∧
      ∀ (Δ α : ℝ), Δ ≥ Δ₄ → α ∈ Set.Ioo (0 : ℝ) 1 →
        |α - (1 / 2 - θ / Real.pi)| ≤ (min ((1 / 2 - θ / Real.pi) / 2) ((1 - (1 / 2 - θ / Real.pi)) / 2)) / 2 →
        |(∑' n : ℤ, rescaledF θ Δ (n + α)) - (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)| ≤
          C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - (1 / 2 - θ / Real.pi)|) := by
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by dsimp only [δ_star]; positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hα_star1 : δ ≤ α_star := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ α_star / 2 := min_le_left _ _
    linarith
  have hα_star2 : α_star ≤ 1 - δ := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    linarith
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c_sin := div_pos hsin_δ_pos (Real.exp_pos _)
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  let C_eval : ℝ := Real.pi ^ 2 / c_sin ^ 2 * (1 / (2 * Real.pi)) + Real.pi ^ 2 / c_sin ^ 2 +
    2 * Real.pi / Real.cos θ * (1 / (2 * Real.pi)) + 2 * Real.pi / Real.cos θ + 1
  refine ⟨1, C_eval, le_rfl, by positivity, fun Δ α hΔ hα hα_near => ?_⟩
  have hΔ_pos : 0 < Δ := by linarith
  have hα1 : δ ≤ α := by
    have h1 := (abs_le.mp hα_near).1
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ α_star / 2 := min_le_left _ _
    linarith
  have hα2 : α ≤ 1 - δ := by
    have h1 := (abs_le.mp hα_near).2
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    linarith
  have h_na_lb : ∀ n : ℤ, δ ≤ |(n : ℝ) + α| := by
    intro n
    rcases le_or_gt (0 : ℤ) n with hn | hn
    · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_pos (by linarith [hα.1])]; linarith
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
      rw [abs_of_neg (by linarith [hα.2])]; linarith
  have hx_ne : ∀ n : ℤ, (n : ℝ) + α ≠ 0 := fun n h0 => by
    have := h_na_lb n; rw [h0, abs_zero] at this; linarith
  have h_summ_F : Summable (fun n : ℤ => rescaledF θ Δ (n + α)) :=
    (rescaledF_summable θ Δ α hΔ hα).of_norm_bounded (fun n => by rw [Real.norm_eq_abs])
  have h_tend_sum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), rescaledF θ Δ (n + α))
      atTop (nhds (∑' n : ℤ, rescaledF θ Δ (n + α))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hs := h_summ_F.hasSum
    rw [HasSum, Metric.tendsto_atTop] at hs
    obtain ⟨s₀, hs₀⟩ := hs ε hε
    refine ⟨s₀.sup Int.natAbs, fun N hN => hs₀ (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n hn => ?_⟩
    have h1 : n.natAbs ≤ N := le_trans (Finset.le_sup hn) hN
    rw [Finset.mem_Icc] at hn ⊢
    omega
  let cot_fn : ℝ → ℂ := fun v =>
    (Real.pi : ℂ) * Complex.cos (Real.pi * (α - Complex.I * v)) / Complex.sin (Real.pi * (α - Complex.I * v))
  have h_cot_ne : ∀ v : ℝ, 0 ≤ v → Complex.sin (Real.pi * (α - Complex.I * v)) ≠ 0 := by
    intro v hv
    have heq : (Real.pi : ℂ) * (α - Complex.I * v) = -(Real.pi * (Complex.I * v - α)) := by ring
    rw [heq, Complex.sin_neg, neg_ne_zero]
    have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv
    exact norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))])
  have h_tend_cot : Tendsto (fun N : ℕ =>
      -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) *
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))).im) -
      Real.sin θ * Δ * (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (n + α) / ((n + α) ^ 2 + Δ ^ 2)))
      atTop (nhds (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
        Real.sin θ * Δ * (cot_fn Δ).re)) := by
    have h_part_sum_eq : ∀ (N : ℕ) (v : ℝ),
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v)) =
          -(1 / (-α + Complex.I * v) + ∑ k ∈ Finset.range N,
            (1 / ((-α + Complex.I * v) + (k + 1 : ℕ)) + 1 / ((-α + Complex.I * v) - (k + 1 : ℕ)))) := by
      intro N v
      induction N with
      | zero =>
        simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, Int.cast_zero,
          zero_add, Finset.range_zero, Finset.sum_empty, add_zero]
        ring
      | succ N ih =>
        have h_icc : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
            insert ((N + 1 : ℕ) : ℤ) (insert (-((N + 1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [h_icc, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
          Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, Finset.sum_range_succ]
        push_cast; ring
    have h_cot_lim : ∀ v ∈ Set.Ioo (0 : ℝ) Δ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v)))
          atTop (nhds (cot_fn v)) := by
      intro v hv
      have hz := pi_cot_tsum_eq (z := -α + Complex.I * v) (by simp [hv.1])
      have h_cot_neg : -(Real.pi : ℂ) * Complex.cos (Real.pi * (-α + Complex.I * v)) / Complex.sin (Real.pi * (-α + Complex.I * v)) =
          cot_fn v := by
        dsimp only [cot_fn]
        have heq : (Real.pi : ℂ) * (-α + Complex.I * v) = -(Real.pi * (α - Complex.I * v)) := by ring
        rw [heq, Complex.cos_neg, Complex.sin_neg]
        ring
      have h_summ_k := summable_inv_add_inv_complex (w := -α + Complex.I * v)
        (fun n h0 => by have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne (-n) (by linarith))
      have h_t := (h_summ_k.hasSum.tendsto_sum_nat.const_add (1 / (-α + Complex.I * v))).neg
      have h_eq_lim : -(1 / (-α + Complex.I * v) + ∑' n : ℕ, (1 / ((-α + Complex.I * v) + (n + 1 : ℕ)) +
          1 / ((-α + Complex.I * v) - (n + 1 : ℕ)))) = cot_fn v := by
        rw [← hz, ← h_cot_neg]; ring
      rw [h_eq_lim] at h_t
      refine h_t.congr (fun N => (h_part_sum_eq N v).symm)
    have h_dom_bd : ∃ C_dom > 0, ∀ (N : ℕ) (v : ℝ), v ∈ Set.Icc 0 Δ →
        ‖∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))‖ ≤ C_dom := by
      let K0 : ℕ := Nat.ceil (2 * (1 + Δ)) + 2
      let C_z : ℝ := ∑' k : ℕ, (1 : ℝ) / (k + 1 : ℝ) ^ 2
      let C_dom : ℝ := 1 / δ + (K0 : ℝ) * (2 / δ) + 4 * (1 + Δ) * C_z + 1
      refine ⟨C_dom, by positivity, fun N v hv => ?_⟩
      rw [h_part_sum_eq N v, norm_neg]
      let z : ℂ := -α + Complex.I * v
      have hz_norm : ‖z‖ ≤ 1 + Δ := by
        calc ‖z‖ ≤ ‖(-α : ℂ)‖ + ‖Complex.I * v‖ := norm_add_le _ _
          _ = |α| + |v| := by simp [Complex.norm_real]
          _ ≤ 1 + Δ := add_le_add (by rw [abs_of_pos hα.1]; exact hα.2.le) (by rw [abs_of_nonneg hv.1]; exact hv.2)
      have hz0 : ‖1 / z‖ ≤ 1 / δ := by
        rw [norm_div, norm_one]
        have hre : δ ≤ ‖z‖ := by
          have : |(-α)| ≤ ‖z‖ := by
            have h1 : z.re = -α := by simp [z]
            rw [← h1]; exact Complex.abs_re_le_norm z
          rw [abs_neg] at this
          have := h_na_lb 0; simp at this; linarith
        exact div_le_div_of_nonneg_left zero_le_one hδ0 hre
      have h_each_k : ∀ k : ℕ, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ ≤
          (if k < K0 then 2 / δ else 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) := by
        intro k
        split_ifs with hk
        · have h1 : δ ≤ ‖z + (k + 1 : ℕ)‖ := by
            have hre : (z + (k + 1 : ℕ)).re = (k + 1 : ℤ) - α := by simp [z]; ring
            have h_lb := h_na_lb (-(k + 1 : ℤ))
            have h_eq : |((-(k + 1 : ℤ) : ℤ) : ℝ) + α| = |(k + 1 : ℤ) - α| := by
              rw [← abs_neg]; push_cast; ring_nf
            rw [← h_eq, ← hre] at h_lb
            exact h_lb.trans (Complex.abs_re_le_norm _)
          have h2 : δ ≤ ‖z - (k + 1 : ℕ)‖ := by
            have hre : (z - (k + 1 : ℕ)).re = -((k + 1 : ℤ) + α) := by simp [z]; ring
            have h_lb := h_na_lb (k + 1 : ℤ)
            have h_eq : |((k + 1 : ℤ) : ℝ) + α| = |-((k + 1 : ℤ) + α)| := by rw [abs_neg]
            rw [← h_eq, ← hre] at h_lb
            exact h_lb.trans (Complex.abs_re_le_norm _)
          calc ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖
              ≤ ‖1 / (z + (k + 1 : ℕ))‖ + ‖1 / (z - (k + 1 : ℕ))‖ := norm_add_le _ _
            _ = 1 / ‖z + (k + 1 : ℕ)‖ + 1 / ‖z - (k + 1 : ℕ)‖ := by simp [norm_div]
            _ ≤ 1 / δ + 1 / δ := add_le_add (div_le_div_of_nonneg_left zero_le_one hδ0 h1)
                (div_le_div_of_nonneg_left zero_le_one hδ0 h2)
            _ = 2 / δ := by ring
        · have hk1_ge : 2 * (1 + Δ) ≤ k + 1 := by
            have : (Nat.ceil (2 * (1 + Δ)) : ℝ) + 2 ≤ k := by exact_mod_cast (not_lt.mp hk)
            linarith [Nat.le_ceil (2 * (1 + Δ))]
          have hne1 : z + (k + 1 : ℕ) ≠ 0 := by
            intro h0; have hre := congr_arg Complex.re h0; simp [z] at hre; linarith [hα.2]
          have hne2 : z - (k + 1 : ℕ) ≠ 0 := by
            intro h0; have hre := congr_arg Complex.re h0; simp [z] at hre; linarith [hα.1]
          have hne3 : z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := by
            rw [sq_sub_sq]; exact mul_ne_zero hne1 hne2
          have heq : 1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ)) =
              2 * z / (z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2) := by
            field_simp [hne1, hne2, hne3]; ring
          rw [heq, norm_div, norm_mul, Complex.norm_ofNat]
          have hden : ((k + 1 : ℝ) ^ 2) / 2 ≤ ‖z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2‖ := by
            have h1 : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
            have h2 : ‖(((k + 1 : ℕ) : ℂ) ^ 2)‖ = (k + 1 : ℝ) ^ 2 := by
              rw [norm_pow, Complex.norm_natCast]; push_cast; rfl
            have h_tri := norm_sub_norm_le (((k + 1 : ℕ) : ℂ) ^ 2) (z ^ 2)
            rw [norm_sub_rev] at h_tri
            have h_z_le : ‖z‖ ^ 2 ≤ (k + 1 : ℝ) ^ 2 / 2 := by
              have h_1d : 1 + Δ ≤ (k + 1 : ℝ) / 2 := by linarith
              calc ‖z‖ ^ 2 ≤ (1 + Δ) ^ 2 := sq_le_sq' (by linarith [norm_nonneg z]) hz_norm
                _ ≤ ((k + 1 : ℝ) / 2) ^ 2 := sq_le_sq' (by linarith) h_1d
                _ = (k + 1 : ℝ) ^ 2 / 4 := by ring
                _ ≤ (k + 1 : ℝ) ^ 2 / 2 := by gcongr; norm_num
            linarith
          calc 2 * ‖z‖ / ‖z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2‖
              ≤ 2 * (1 + Δ) / ((k + 1 : ℝ) ^ 2 / 2) :=
                div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
            _ = 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2 := by field_simp; ring
      have h_sum_k : ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ ≤
          (K0 : ℝ) * (2 / δ) + 4 * (1 + Δ) * C_z := by
        have h1 : ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ ≤
            ∑ k ∈ Finset.range N, (if k < K0 then 2 / δ else 0) +
            ∑ k ∈ Finset.range N, (4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun k _ => ?_
          refine (h_each_k k).trans ?_
          split_ifs
          · exact le_add_of_nonneg_right (by positivity)
          · exact le_add_of_nonneg_left (by positivity)
        have h2 : ∑ k ∈ Finset.range N, (if k < K0 then (2 / δ : ℝ) else 0) ≤ (K0 : ℝ) * (2 / δ) := by
          have h_sub : (Finset.range N).filter (· < K0) ⊆ Finset.range K0 := fun k hk => by
            rw [Finset.mem_filter] at hk; exact Finset.mem_range.mpr hk.2
          rw [← Finset.sum_filter (p := (· < K0))]
          calc ∑ _k ∈ (Finset.range N).filter (· < K0), (2 / δ : ℝ)
              ≤ ∑ _k ∈ Finset.range K0, (2 / δ : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
            _ = (K0 : ℝ) * (2 / δ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have h3 : ∑ k ∈ Finset.range N, (4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) ≤ 4 * (1 + Δ) * C_z := by
          have h_s : Summable (fun k : ℕ => 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) :=
            (summable_one_div_sq_nat.mul_left (4 * (1 + Δ))).congr (fun k => by ring)
          calc ∑ k ∈ Finset.range N, (4 * (1 + Δ) / (k + 1 : ℝ) ^ 2)
              ≤ ∑' k : ℕ, (4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) := h_s.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
            _ = 4 * (1 + Δ) * C_z := by
                rw [show (fun k : ℕ => 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) = fun k : ℕ => (4 * (1 + Δ)) * (1 / (k + 1 : ℝ) ^ 2) by ext k; ring,
                  tsum_mul_left]
        linarith
      calc ‖1 / z + ∑ k ∈ Finset.range N, (1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ)))‖
          ≤ ‖1 / z‖ + ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
        _ ≤ 1 / δ + ((K0 : ℝ) * (2 / δ) + 4 * (1 + Δ) * C_z) := add_le_add hz0 h_sum_k
        _ ≤ C_dom := by dsimp only [C_dom]; linarith
    obtain ⟨C_dom, hC_dom, h_dom⟩ := h_dom_bd
    have h_int_tend : Tendsto (fun N : ℕ => ∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) *
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))).im)
        atTop (nhds (∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im)) := by
      simp_rw [intervalIntegral.integral_of_le hΔ_pos.le]
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => C_dom) ?_
        (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) ?_ ?_
      · intro N
        refine (Complex.continuous_im.comp (continuous_const.mul (continuous_finset_sum _ fun n _ =>
          continuous_const.div (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)) fun v => ?_))).aestronglyMeasurable
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
      · intro N
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with v hv
        rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        exact h_dom N v ⟨hv.1.le, hv.2⟩
      · rw [ae_restrict_iff' measurableSet_Ioc]
        have h_ae : ∀ᵐ v : ℝ ∂volume, v ∈ Set.Ioc 0 Δ → v ∈ Set.Ioo 0 Δ := by
          filter_upwards [ae_iff.mpr (by simp : volume {v : ℝ | v = Δ} = 0)] with v hv h1
          exact ⟨h1.1, lt_of_le_of_ne h1.2 hv⟩
        filter_upwards [h_ae] with v hv1 hv2
        exact (Complex.imCLM.continuous.continuousAt.comp ((continuousAt_const).mul continuousAt_id)).tendsto.comp
          (h_cot_lim v (hv1 hv2))
    have h_bd_tend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (n + α) / ((n + α) ^ 2 + Δ ^ 2))
        atTop (nhds ((cot_fn Δ).re)) := by
      have hz := pi_cot_tsum_eq (z := -α + Complex.I * Δ) (by simp [hΔ_pos])
      have h_cot_neg : -(Real.pi : ℂ) * Complex.cos (Real.pi * (-α + Complex.I * Δ)) / Complex.sin (Real.pi * (-α + Complex.I * Δ)) =
          cot_fn Δ := by
        dsimp only [cot_fn]
        have heq : (Real.pi : ℂ) * (-α + Complex.I * Δ) = -(Real.pi * (α - Complex.I * Δ)) := by ring
        rw [heq, Complex.cos_neg, Complex.sin_neg]; ring
      have h_summ_k := summable_inv_add_inv_complex (w := -α + Complex.I * Δ)
        (fun n h0 => by have him := congr_arg Complex.im h0; simp at him; linarith)
      have h_t := (h_summ_k.hasSum.tendsto_sum_nat.const_add (1 / (-α + Complex.I * Δ))).neg
      have h_eq_lim : -(1 / (-α + Complex.I * Δ) + ∑' n : ℕ, (1 / ((-α + Complex.I * Δ) + (n + 1 : ℕ)) +
          1 / ((-α + Complex.I * Δ) - (n + 1 : ℕ)))) = cot_fn Δ := by
        rw [← hz, ← h_cot_neg]; ring
      rw [h_eq_lim] at h_t
      have h_re_t := Complex.reCLM.continuous.continuousAt.tendsto.comp h_t
      refine h_re_t.congr (fun N => ?_)
      rw [Complex.reCLM_apply, ← h_part_sum_eq N Δ, Complex.re_sum]
      congr 1; ext n
      have hden : (((n + α : ℝ) : ℂ) - Complex.I * Δ) * (((n + α : ℝ) : ℂ) + Complex.I * Δ) =
          (((n + α) ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by push_cast; ring_nf; simp [Complex.I_sq]; ring
      have hne : ((n + α : ℝ) : ℂ) - Complex.I * Δ ≠ 0 := by intro h0; have him := congr_arg Complex.im h0; simp at him; linarith
      have hinv : 1 / (((n + α : ℝ) : ℂ) - Complex.I * Δ) = (((n + α : ℝ) : ℂ) + Complex.I * Δ) / (((n + α) ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
        rw [div_eq_div_iff hne (Complex.ofReal_ne_zero.mpr (by positivity)), one_mul]; exact hden.symm
      rw [hinv, Complex.div_ofReal_re]; simp
    exact (h_int_tend.neg).sub (h_bd_tend.const_mul (Real.sin θ * Δ))
  have h_eq_fin : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), rescaledF θ Δ (n + α) =
        -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) *
          ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))).im) -
        Real.sin θ * Δ * (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (n + α) / ((n + α) ^ 2 + Δ ^ 2)) := by
    intro N
    simp_rw [rescaledF_integral_rep θ Δ _ hΔ_pos (hx_ne _)]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h_int_fin : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        IntervalIntegrable (fun v : ℝ => (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)).im) volume 0 Δ := by
      intro n _
      refine (Complex.continuous_im.comp_continuousOn (continuousOn_const.div (by fun_prop) fun v _ h0 => ?_)).intervalIntegrable
      have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
    have h_sum_int : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ v in Set.Ioo (0 : ℝ) Δ,
        (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)).im =
        ∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) *
          ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))).im := by
      simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hΔ_pos.le]
      rw [← intervalIntegral.integral_finset_sum h_int_fin]
      congr 1; ext v
      rw [Finset.mul_sum, Complex.im_sum]
      congr 1; ext n; ring_nf
    rw [h_sum_int, ← Finset.mul_sum]
    congr 2
    ext n; ring
  have h_sum_val : ∑' n : ℤ, rescaledF θ Δ (n + α) =
      -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
        Real.sin θ * Δ * (cot_fn Δ).re :=
    tendsto_nhds_unique h_tend_sum (h_tend_cot.congr (fun N => (h_eq_fin N).symm))
  let cot_star : ℝ → ℂ := fun v =>
    (Real.pi : ℂ) * Complex.cos (Real.pi * (α_star - Complex.I * v)) / Complex.sin (Real.pi * (α_star - Complex.I * v))
  have h_cot_diff : ∀ v : ℝ, 0 ≤ v →
      ‖cot_fn v - cot_star v‖ ≤ (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    let z₁ : ℂ := Real.pi * (α - Complex.I * v)
    let z₂ : ℂ := Real.pi * (α_star - Complex.I * v)
    have hs1 : c_sin * Real.exp (Real.pi * v) ≤ ‖Complex.sin z₁‖ := by
      have heq : z₁ = -(Real.pi * (Complex.I * v - α)) := by dsimp only [z₁]; ring
      rw [heq, Complex.sin_neg, norm_neg]
      exact sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv
    have hs2 : c_sin * Real.exp (Real.pi * v) ≤ ‖Complex.sin z₂‖ := by
      have heq : z₂ = -(Real.pi * (Complex.I * v - α_star)) := by dsimp only [z₂]; ring
      rw [heq, Complex.sin_neg, norm_neg]
      exact sin_pi_iv_beta_lb hδ0 hδ1 hα_star1 hα_star2 v hv
    have hne1 : Complex.sin z₁ ≠ 0 := norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))])
    have hne2 : Complex.sin z₂ ≠ 0 := norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))])
    have h_id : cot_fn v - cot_star v = (Real.pi : ℂ) * Complex.sin (z₂ - z₁) / (Complex.sin z₁ * Complex.sin z₂) := by
      dsimp only [cot_fn, cot_star]
      rw [Complex.sin_sub]
      field_simp [hne1, hne2]; ring
    have h_zdiff : ‖Complex.sin (z₂ - z₁)‖ ≤ Real.pi * |α - α_star| := by
      have heq : z₂ - z₁ = ((Real.pi * (α_star - α) : ℝ) : ℂ) := by dsimp only [z₁, z₂]; push_cast; ring
      rw [heq, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
      calc |Real.sin (Real.pi * (α_star - α))| ≤ |Real.pi * (α_star - α)| := Real.abs_sin_le_abs
        _ = Real.pi * |α - α_star| := by rw [abs_mul, abs_of_pos Real.pi_pos, abs_sub_comm]
    rw [h_id, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_mul]
    have hden : c_sin ^ 2 * Real.exp (2 * Real.pi * v) ≤ ‖Complex.sin z₁‖ * ‖Complex.sin z₂‖ := by
      calc c_sin ^ 2 * Real.exp (2 * Real.pi * v) = (c_sin * Real.exp (Real.pi * v)) * (c_sin * Real.exp (Real.pi * v)) := by
            rw [show 2 * Real.pi * v = Real.pi * v + Real.pi * v by ring, Real.exp_add]; ring
        _ ≤ ‖Complex.sin z₁‖ * ‖Complex.sin z₂‖ := mul_le_mul hs1 hs2 (by positivity) (norm_nonneg _)
    calc Real.pi * ‖Complex.sin (z₂ - z₁)‖ / (‖Complex.sin z₁‖ * ‖Complex.sin z₂‖)
        ≤ Real.pi * (Real.pi * |α - α_star|) / (c_sin ^ 2 * Real.exp (2 * Real.pi * v)) :=
          div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
      _ = (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
          rw [Real.exp_neg]; field_simp [hc_pos.ne']; ring
  let rem_fn : ℝ → ℂ := fun v =>
    (Real.pi : ℂ) * (-Complex.I * Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) /
      Complex.cos (θ + Complex.I * Real.pi * v))
  have h_cot_star_eq : ∀ v : ℝ, cot_star v = (Real.pi : ℂ) * Complex.I + rem_fn v := by
    intro v
    dsimp only [cot_star, rem_fn]
    have h1 : (Real.pi : ℂ) * (α_star - Complex.I * v) = Real.pi / 2 - (θ + Complex.I * Real.pi * v) := by
      dsimp only [α_star]; push_cast; field_simp [Real.pi_ne_zero]; ring
    rw [h1, Complex.cos_pi_div_two_sub, Complex.sin_pi_div_two_sub]
    have hcos : Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := cos_ne_zero_of_abs_lt hθ
    have h_euler : Complex.sin (θ + Complex.I * Real.pi * v) - Complex.I * Complex.cos (θ + Complex.I * Real.pi * v) =
        -Complex.I * Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) := by
      rw [Complex.exp_mul_I]; ring_nf; simp [Complex.I_sq]; ring
    field_simp [hcos]
    linear_combination (Real.pi : ℂ) * h_euler
  have h_rem_bd : ∀ v : ℝ, 0 ≤ v → ‖rem_fn v‖ ≤ (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    dsimp only [rem_fn]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_div, norm_mul,
      norm_neg, Complex.norm_I, one_mul]
    have hexp : ‖Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v))‖ = Real.exp (-Real.pi * v) := by
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.add_re]; ring
    have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤ ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
      have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤ ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
        have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
          rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
        have h1 : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
          have := Real.cosh_sq (Real.pi * v); have := Real.cos_sq_add_sin_sq θ
          nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
        rw [cos_normSq_eq]; nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
    rw [hexp]
    calc Real.pi * (Real.exp (-Real.pi * v) / ‖Complex.cos (θ + Complex.I * Real.pi * v)‖)
        ≤ Real.pi * (Real.exp (-Real.pi * v) / ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by gcongr
      _ = (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v) := by
          rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
          field_simp [hcos_pos.ne']
  have h_rem_int_Ioi : ∫ v in Set.Ioi (0 : ℝ), -(Complex.exp (-Complex.I * θ) * rem_fn v).im = 2 * envelopeC θ := by
    let G : ℝ → ℝ := fun v =>
      -(Complex.exp (-Complex.I * θ) * Complex.I *
        Complex.log (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v)))).im
    have h_slit : ∀ v : ℝ, 0 ≤ v → 0 < (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))).re := by
      intro v hv
      by_cases hv0 : v = 0
      · subst hv0
        have heq : 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * (0 : ℝ))) =
            1 + Complex.exp (Complex.I * (2 * θ)) := by ring_nf
        rw [heq, Complex.exp_mul_I]
        simp only [Complex.add_re, Complex.one_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.sin_ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
        have h1 : 1 + Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 := by rw [Real.cos_two_mul]; ring
        rw [h1]; positivity
      · have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
        have hnorm : ‖Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))‖ < 1 := by
          rw [Complex.norm_exp, Real.exp_lt_one_iff]
          have hre : (2 * Complex.I * ((θ : ℂ) + Complex.I * Real.pi * v)).re = -2 * Real.pi * v := by
            simp [Complex.mul_re, Complex.add_re]; ring
          rw [hre]; nlinarith [Real.pi_pos]
        have hre : (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))).re =
            1 + (Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))).re := by simp
        rw [hre]
        linarith [Complex.re_le_norm (Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))),
          neg_le_abs (Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))).re,
          Complex.abs_re_le_norm (Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v)))]
    have hG_deriv : ∀ v ∈ Set.Ioi (0 : ℝ), HasDerivAt G (-(Complex.exp (-Complex.I * θ) * rem_fn v).im) v := by
      intro v hv
      have h_inner : HasDerivAt (fun t : ℝ => 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * t)))
          ((-2 * Real.pi : ℂ) * Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) v := by
        have hd1 : HasDerivAt (fun t : ℝ => 2 * Complex.I * ((θ : ℂ) + Complex.I * Real.pi * t)) (-2 * Real.pi : ℂ) v := by
          have ha : HasDerivAt (fun t : ℝ => (θ : ℂ) + Complex.I * Real.pi * t) (Complex.I * Real.pi) v := by
            simpa using (hasDerivAt_const v (θ : ℂ)).add ((hasDerivAt_id v).ofReal_comp.const_mul (Complex.I * Real.pi))
          exact (ha.const_mul (2 * Complex.I)).congr_deriv (by ring_nf; simp [Complex.I_sq]; ring)
        simpa [mul_comm] using (hasDerivAt_const v (1 : ℂ)).add hd1.cexp
      have h_log : HasDerivAt (fun t : ℝ => Complex.log (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * t))))
          (((-2 * Real.pi : ℂ) * Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) /
            (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v)))) v :=
        h_inner.clog (Complex.mem_slitPlane_iff.mpr (Or.inl (h_slit v hv.le)))
      have h_mul := h_log.const_mul (Complex.exp (-Complex.I * θ) * Complex.I)
      have h_im := (Complex.imCLM.hasDerivAt.comp v h_mul).neg
      refine h_im.congr_deriv ?_
      dsimp only [Complex.imCLM_apply]
      congr 2
      dsimp only [rem_fn]
      have h_cos_eq : 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v)) =
          2 * Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) * Complex.cos (θ + Complex.I * Real.pi * v) := by
        have hcos_def : Complex.cos (θ + Complex.I * Real.pi * v) =
            (Complex.exp ((θ + Complex.I * Real.pi * v) * Complex.I) +
              Complex.exp (-(θ + Complex.I * Real.pi * v) * Complex.I)) / 2 := by
          unfold Complex.cos; ring_nf
        rw [hcos_def, ← Complex.exp_add]
        have he1 : Complex.I * (θ + Complex.I * Real.pi * v) + (θ + Complex.I * Real.pi * v) * Complex.I =
            2 * Complex.I * (θ + Complex.I * Real.pi * v) := by ring
        have he2 : Complex.I * (θ + Complex.I * Real.pi * v) + -(θ + Complex.I * Real.pi * v) * Complex.I = 0 := by ring
        rw [mul_div_cancel₀ _ two_ne_zero, mul_add, ← Complex.exp_add, ← Complex.exp_add, he1, he2, Complex.exp_zero]
        ring
      have hcos_ne : Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := cos_ne_zero_of_abs_lt hθ
      have hexp_ne : Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) ≠ 0 := Complex.exp_ne_zero _
      rw [h_cos_eq]
      have he2 : Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v)) =
          Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) ^ 2 := by
        rw [← Complex.exp_nat_mul]; congr 1; ring
      rw [he2]
      field_simp [hcos_ne, hexp_ne]; ring
    have h_int_r : IntegrableOn (fun v : ℝ => -(Complex.exp (-Complex.I * θ) * rem_fn v).im) (Set.Ioi 0) := by
      have h_e : IntegrableOn (fun v : ℝ => (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
        refine (hc.norm.congr (Eventually.of_forall fun v => ?_)).const_mul _
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine h_e.mono' ?_ ?_
      · refine (Complex.continuous_im.comp (continuous_const.mul (continuous_const.mul (Continuous.div (by fun_prop)
          (Complex.continuous_cos.comp (by fun_prop)) fun v => cos_ne_zero_of_abs_lt hθ)))).neg.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [Real.norm_eq_abs, abs_neg]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        exact h_rem_bd v hv.le
    have h_cont : ContinuousAt G 0 := by
      refine (Complex.imCLM.continuous.continuousAt.comp (continuousAt_const.mul ?_)).neg
      refine (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (h_slit 0 le_rfl)))).continuousAt.comp ?_
      fun_prop
    have hG_val : G 0 = -2 * envelopeC θ := by
      dsimp only [G]
      have heq : 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * (0 : ℝ))) =
          Complex.exp ((Real.log (2 * Real.cos θ) : ℂ) + Complex.I * θ) := by
        rw [Complex.ofReal_zero, mul_zero, add_zero, Complex.exp_add, Complex.ofReal_log (by positivity),
          show 2 * Complex.I * (θ : ℂ) = Complex.I * θ + Complex.I * θ by ring,
          Complex.exp_add]
        have hcos_def : Complex.cos (θ : ℂ) = (Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I)) / 2 := by
          unfold Complex.cos; ring_nf
        rw [← Complex.ofReal_cos, hcos_def]
        push_cast; rw [Complex.exp_mul_I, show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]; simp [Complex.cos_neg, Complex.sin_neg]
        ring_nf; simp [Complex.I_sq]; ring
      rw [heq, Complex.log_exp (by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, mul_zero, zero_mul, add_zero, zero_add, one_mul]
        linarith [(abs_lt.mp hθ).1, Real.pi_pos]) (by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, mul_zero, zero_mul, add_zero, zero_add, one_mul]
        linarith [(abs_lt.mp hθ).2, Real.pi_pos])]
      have hexp : Complex.exp (-Complex.I * θ) = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
        rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
        simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin, Complex.I_sq]
        ring
      rw [hexp]
      unfold envelopeC
      have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
      have hi3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
      simp only [sub_mul, add_mul, mul_add, mul_sub, hi2, hi3, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hG_inf : Tendsto G atTop (nhds 0) := by
      have h1 : Tendsto (fun v : ℝ => 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) atTop (nhds 1) := by
        have h0 : Tendsto (fun v : ℝ => Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) atTop (nhds 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have h_n : ∀ v : ℝ, ‖Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))‖ = Real.exp (-2 * Real.pi * v) := by
            intro v; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.add_re]; ring
          simp_rw [h_n]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -2 * Real.pi < 0))
        simpa using tendsto_const_nhds.add h0
      have h_log1 : Tendsto (fun v : ℝ => Complex.log (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))))
          atTop (nhds 0) := by
        have hc := (Complex.hasDerivAt_log (by norm_num : (1 : ℂ) ∈ Complex.slitPlane)).continuousAt.tendsto.comp h1
        simpa [Function.comp_def, Complex.log_one] using hc
      have hG_eq : G = fun v : ℝ => -(Complex.imCLM (Complex.exp (-Complex.I * θ) * Complex.I *
          Complex.log (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))))) := rfl
      rw [hG_eq]
      simpa using (Complex.imCLM.continuous.continuousAt.tendsto.comp (tendsto_const_nhds.mul h_log1)).neg
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto h_cont.continuousWithinAt hG_deriv h_int_r hG_inf
    rw [hG_val] at hres
    linarith
  have h_int_cot : IntervalIntegrable (fun v : ℝ => (Complex.exp (-Complex.I * θ) * cot_fn v).im) volume 0 Δ := by
    refine (Complex.continuous_im.comp_continuousOn (continuousOn_const.mul ?_)).intervalIntegrable
    refine ContinuousOn.div (continuousOn_const.mul (Complex.continuous_cos.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)))
      (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) fun v hv => ?_
    rw [Set.uIcc_of_le hΔ_pos.le] at hv
    exact h_cot_ne v hv.1
  have h_int_rem : IntervalIntegrable (fun v : ℝ => (Complex.exp (-Complex.I * θ) * rem_fn v).im) volume 0 Δ := by
    refine (Complex.continuous_im.comp_continuousOn (continuousOn_const.mul (continuousOn_const.mul
      (ContinuousOn.div (by fun_prop) (Complex.continuous_cos.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _))
      fun v _ => cos_ne_zero_of_abs_lt hθ)))).intervalIntegrable
  have h_int_pi : IntervalIntegrable (fun v : ℝ => (Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I)).im) volume 0 Δ :=
    intervalIntegrable_const
  have h_cot_star_split : -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im) =
      -Real.pi * Δ * Real.cos θ + ∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im := by
    have h_eq : (fun v : ℝ => (Complex.exp (-Complex.I * θ) * cot_star v).im) =
        fun v : ℝ => (Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I)).im +
          (Complex.exp (-Complex.I * θ) * rem_fn v).im := by
      ext v; rw [h_cot_star_eq v, mul_add, Complex.add_im]
    rw [h_eq, intervalIntegral.integral_add h_int_pi h_int_rem, neg_add_rev, ← intervalIntegral.integral_neg]
    have h_pi_val : -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I)).im) =
        -Real.pi * Δ * Real.cos θ := by
      have hexp : Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I) =
          ((Real.pi * Real.sin θ : ℝ) : ℂ) + ((Real.pi * Real.cos θ : ℝ) : ℂ) * Complex.I := by
        rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_mul_I]
        simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
        linear_combination -(Real.sin θ * Real.pi : ℂ) * Complex.I_sq
      simp_rw [hexp]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, mul_one, add_zero, zero_add]
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
    linarith
  have h_err1 : |∫ v in (0 : ℝ)..Δ, ((Complex.exp (-Complex.I * θ) * cot_fn v).im -
      (Complex.exp (-Complex.I * θ) * cot_star v).im)| ≤ (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * (1 / (2 * Real.pi)) := by
    rw [intervalIntegral.integral_of_le hΔ_pos.le, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h_e_int : IntegrableOn (fun v : ℝ => (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
      have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      have hr : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hr.const_mul _
    have h_mono1 : ∫ v in Set.Ioc 0 Δ, ‖(Complex.exp (-Complex.I * θ) * cot_fn v).im -
          (Complex.exp (-Complex.I * θ) * cot_star v).im‖ ≤
        ∫ v in Set.Ioc 0 Δ, (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
      refine setIntegral_mono_on ?_ (h_e_int.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun v hv => ?_
      · have h_eq_cs : (fun v : ℝ => (Complex.exp (-Complex.I * θ) * cot_star v).im) =
            fun v : ℝ => (Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I)).im +
              (Complex.exp (-Complex.I * θ) * rem_fn v).im := by
          ext v; rw [h_cot_star_eq v, mul_add, Complex.add_im]
        have h_int_cs : IntervalIntegrable (fun v : ℝ => (Complex.exp (-Complex.I * θ) * cot_star v).im) volume 0 Δ := by
          rw [h_eq_cs]; exact h_int_pi.add h_int_rem
        exact (h_int_cot.sub h_int_cs).1.norm
      · rw [Real.norm_eq_abs, ← Complex.sub_im, ← mul_sub]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        exact h_cot_diff v hv.1.le
    have h_mono2 : ∫ v in Set.Ioc 0 Δ, (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v) ≤
        ∫ v in Set.Ioi 0, (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * v) :=
      setIntegral_mono_set h_e_int (Eventually.of_forall fun _ => by positivity) Set.Ioc_subset_Ioi_self.eventuallyLE
    have h_val : ∫ v in Set.Ioi (0 : ℝ), Real.exp (-2 * Real.pi * v) = 1 / (2 * Real.pi) := by
      have h_lim : Tendsto (fun v : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
        have h1 : Tendsto (fun v : ℝ => Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(2 * Real.pi) < 0))
        simpa using h1.const_mul (-(1 / (2 * Real.pi)))
      have h_int : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h_d : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * t))
          (Real.exp (-2 * Real.pi * v)) v := by
        intro v _
        have hd := ((hasDerivAt_id v).const_mul (-2 * Real.pi)).exp.const_mul (-(1 / (2 * Real.pi)))
        refine hd.congr_deriv ?_; dsimp only [id]; field_simp [Real.pi_ne_zero]
      simpa using integral_Ioi_of_hasDerivAt_of_tendsto' h_d h_int h_lim
    simp_rw [integral_const_mul] at h_mono1 h_mono2; rw [h_val] at h_mono2
    linarith
  have h_err2 : |(∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) - 2 * envelopeC θ| ≤
      (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) := by
    have h_int_r : IntegrableOn (fun v : ℝ => -(Complex.exp (-Complex.I * θ) * rem_fn v).im) (Set.Ioi 0) := by
      have h_e : IntegrableOn (fun v : ℝ => (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
        refine (hc.norm.congr (Eventually.of_forall fun v => ?_)).const_mul _
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine h_e.mono' ?_ ?_
      · refine (Complex.continuous_im.comp (continuous_const.mul (continuous_const.mul (Continuous.div (by fun_prop)
          (Complex.continuous_cos.comp (by fun_prop)) fun v => cos_ne_zero_of_abs_lt hθ)))).neg.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [Real.norm_eq_abs, abs_neg]; refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        exact h_rem_bd v hv.le
    have h_split : 2 * envelopeC θ = (∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) +
        ∫ v in Set.Ioi Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im := by
      have h_set : Set.Ioi (0 : ℝ) = Set.Ioc 0 Δ ∪ Set.Ioi Δ := by
        ext v; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        exact ⟨fun h => (le_or_gt v Δ).elim (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr h'),
          fun h => h.elim (fun a => a.1) (fun a => by linarith)⟩
      rw [← h_rem_int_Ioi, intervalIntegral.integral_of_le hΔ_pos.le, h_set,
        setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h_int_r.mono_set Set.Ioc_subset_Ioi_self) (h_int_r.mono_set (Set.Ioi_subset_Ioi (by linarith)))]
    rw [show (∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) - 2 * envelopeC θ =
        -(∫ v in Set.Ioi Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) by linarith, abs_neg, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h_e_int : IntegrableOn (fun v : ℝ => (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v)) (Set.Ioi Δ) := by
      have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi Δ) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) Δ
      refine (hc.norm.congr (Eventually.of_forall fun v => ?_)).const_mul _
      dsimp only
      rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h_mono : ∫ v in Set.Ioi Δ, ‖-(Complex.exp (-Complex.I * θ) * rem_fn v).im‖ ≤
        ∫ v in Set.Ioi Δ, (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * v) := by
      refine setIntegral_mono_on (h_int_r.mono_set (Set.Ioi_subset_Ioi (by linarith))).norm h_e_int measurableSet_Ioi fun v hv => ?_
      rw [Real.norm_eq_abs, abs_neg]; refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact h_rem_bd v (by linarith [hv.out])
    have h_val : ∫ v in Set.Ioi Δ, Real.exp (-2 * Real.pi * v) = (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) := by
      have h_lim : Tendsto (fun v : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
        have h1 : Tendsto (fun v : ℝ => Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(2 * Real.pi) < 0))
        simpa using h1.const_mul (-(1 / (2 * Real.pi)))
      have h_int : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi Δ) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi Δ) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) Δ
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h_d : ∀ v ∈ Set.Ici Δ, HasDerivAt (fun t : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * t))
          (Real.exp (-2 * Real.pi * v)) v := by
        intro v _
        have hd := ((hasDerivAt_id v).const_mul (-2 * Real.pi)).exp.const_mul (-(1 / (2 * Real.pi)))
        refine hd.congr_deriv ?_; dsimp only [id]; field_simp [Real.pi_ne_zero]
      have hres := integral_Ioi_of_hasDerivAt_of_tendsto' h_d h_int h_lim
      linarith
    rw [integral_const_mul, h_val] at h_mono
    linarith
  have h_err3 : |Real.sin θ * Δ * (cot_fn Δ).re| ≤
      Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
        (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ)) := by
    have h_re_eq : (cot_fn Δ).re = (cot_fn Δ - cot_star Δ + rem_fn Δ).re := by
      rw [show cot_fn Δ - cot_star Δ + rem_fn Δ = cot_fn Δ - (Real.pi : ℂ) * Complex.I by
        rw [h_cot_star_eq Δ]; ring, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, sub_zero]
    rw [h_re_eq, abs_mul, abs_mul, abs_of_pos hΔ_pos]
    have h_sin1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have h_re_bd : |(cot_fn Δ - cot_star Δ + rem_fn Δ).re| ≤
        (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
        (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ) := by
      refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
      exact add_le_add (h_cot_diff Δ hΔ_pos.le) (h_rem_bd Δ hΔ_pos.le)
    calc |Real.sin θ| * Δ * |(cot_fn Δ - cot_star Δ + rem_fn Δ).re|
        ≤ 1 * Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
            (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ)) := by gcongr
      _ = _ := by ring
  have h_exp_le : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
    have he := Real.add_one_le_exp (2 * Real.pi * Δ)
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    have h1 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith
    rw [show (-2 * Real.pi * Δ : ℝ) = -(2 * Real.pi * Δ) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    exact h1.trans_eq (one_mul _).symm
  have h_exp_le2 : Real.exp (-2 * Real.pi * Δ) ≤ Δ * Real.exp (-2 * Real.pi * Δ) :=
    le_mul_of_one_le_left (Real.exp_pos _).le hΔ
  rw [h_sum_val]
  have h_int_sub : -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
      (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im)) =
      -(∫ v in (0 : ℝ)..Δ, ((Complex.exp (-Complex.I * θ) * cot_fn v).im -
        (Complex.exp (-Complex.I * θ) * cot_star v).im)) := by
    rw [intervalIntegral.integral_sub h_int_cot (by
      have h_eq : (fun v : ℝ => (Complex.exp (-Complex.I * θ) * cot_star v).im) =
          fun v : ℝ => (Complex.exp (-Complex.I * θ) * ((Real.pi : ℂ) * Complex.I)).im +
            (Complex.exp (-Complex.I * θ) * rem_fn v).im := by
        ext v; rw [h_cot_star_eq v, mul_add, Complex.add_im]
      rw [h_eq]; exact h_int_pi.add h_int_rem)]
    ring
  calc |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) - Real.sin θ * Δ * (cot_fn Δ).re -
        (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)|
      = |(-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
          (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))) +
          ((∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) - 2 * envelopeC θ) -
          Real.sin θ * Δ * (cot_fn Δ).re| := by
        congr 1; rw [h_cot_star_split]; ring
    _ ≤ |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
          (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))| +
          |(∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) - 2 * envelopeC θ| +
          |Real.sin θ * Δ * (cot_fn Δ).re| := by
        calc |(_ + _) - _| ≤ |_ + _| + |_| := abs_sub _ _
          _ ≤ (|_| + |_|) + |_| := add_le_add_right (abs_add_le _ _) _
    _ ≤ (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * (1 / (2 * Real.pi)) +
          (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) +
          Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
            (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ)) := by
        rw [h_int_sub, abs_neg]
        exact add_le_add (add_le_add h_err1 h_err2) h_err3
    _ ≤ C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) := by
        have h_t1 : Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ)) ≤
            (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| := by
          calc Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ))
              = (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
            _ ≤ (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * 1 := by gcongr
            _ = (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| := mul_one _
        have h_t2 : (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) ≤
            (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
        have h_pos1 : 0 ≤ Δ * Real.exp (-2 * Real.pi * Δ) := by positivity
        have h_pos2 : 0 ≤ |α - α_star| := abs_nonneg _
        have h_t3 : (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) +
            Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
              (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ)) ≤
            (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) +
            (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| +
            (2 * Real.pi / Real.cos θ) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by
          calc _ = (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) +
                  Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ)) +
                  (2 * Real.pi / Real.cos θ) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
            _ ≤ _ := by gcongr
        have h_s1 : (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * (1 / (2 * Real.pi)) ≤
            (Real.pi ^ 2 / c_sin ^ 2 * (1 / (2 * Real.pi))) * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) := by
          rw [mul_assoc _ |α - α_star| _, mul_comm |α - α_star| _, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h_pos1) (by positivity)
        have h_s2 : (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) ≤
            (2 * Real.pi / Real.cos θ * (1 / (2 * Real.pi))) * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h_pos2) (by positivity)
        have h_s3 : (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| ≤
            (Real.pi ^ 2 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h_pos1) (by positivity)
        have h_s4 : (2 * Real.pi / Real.cos θ) * (Δ * Real.exp (-2 * Real.pi * Δ)) ≤
            (2 * Real.pi / Real.cos θ) * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h_pos2) (by positivity)
        dsimp only [C_eval]
        linarith

end PolarEvaluation
