import PolarEvaluation.AsymmetricMajorantEvalA
import PolarEvaluation.AsymmetricMajorantEvalB

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

set_option maxHeartbeats 800000 in
/-- **Theorem 1.6** (Asymmetric Beurling–Selberg majorant `M_{θ,Δ}`). -/
theorem asymmetric_majorant (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₀ C_sup C_L1 C_err : ℝ), Δ₀ ≥ 1 ∧ C_sup > 0 ∧ C_L1 > 0 ∧ C_err > 0 ∧
      ∀ Δ ≥ Δ₀, ∃ (α : ℝ) (M_entire : ℂ → ℂ),
        α ∈ Set.Ioo (0 : ℝ) 1 ∧
        HasExponentialType M_entire (2 * Real.pi * Δ) ∧
        (∀ x : ℝ, (M_entire x).im = 0 ∧ (M_entire x).re = majorantM θ Δ α x) ∧
        Integrable (fun x : ℝ => majorantM θ Δ α x - kernelK θ x) ∧
        (∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x| ≤ C_sup * Real.log Δ) ∧
        (∫ x : ℝ, |majorantM θ Δ α x|) ≤ C_L1 ∧
        (∀ x : ℝ, x ≠ 0 → majorantM θ Δ α x ≥ kernelK θ x) ∧
        |(∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) - 2 * envelopeC θ / Δ| ≤
          C_err * Real.exp (-2 * Real.pi * Δ) := by
  obtain ⟨Δ₁, C_α, hΔ₁, hC_α, h_opt⟩ := optimal_lattice_shift θ hθ
  obtain ⟨⟨c_J, hc_J, hJ_all⟩, ⟨c'_J, hc'_J, hJ_small⟩⟩ := limitingJ_lower_bounds θ hθ
  obtain ⟨Δ₂, C_err1, hΔ₂, hC_err1, h_diff_bd⟩ := majorant_contour_diff_bounds θ hθ
  obtain ⟨Δ₃, C_sup, C_L1, hΔ₃, hC_sup, hC_L1, h_sup_L1⟩ := majorantM_sup_and_L1_bounds θ hθ
  obtain ⟨Δ₄, C_eval, hΔ₄, hC_eval, h_tsum_eval⟩ := tsum_rescaledF_eval θ hθ
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  have hδ_star : 0 < δ_star := lt_min (by linarith [hα_star.1]) (by linarith [hα_star.2])
  let C_err : ℝ := C_eval * (1 + C_α)
  let Δ₀ : ℝ := max (max (max Δ₁ Δ₂) (max Δ₃ Δ₄))
    (max (2 * C_α / δ_star + 1) (max (C_err1 * (1 + C_α) / c'_J + 1) (C_err1 * (1 + C_α) / (c_J / 2) + 1)))
  have hΔ₀ : Δ₀ ≥ 1 := le_trans hΔ₁ (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine ⟨Δ₀, C_sup, C_L1, C_err, hΔ₀, hC_sup, hC_L1, by positivity, fun Δ hΔ => ?_⟩
  have hΔ_ge_1 : Δ ≥ 1 := le_trans hΔ₀ hΔ
  have hΔ_pos : 0 < Δ := by linarith
  have hΔ_ge_Δ₁ : Δ ≥ Δ₁ := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hΔ
  have hΔ_ge_Δ₂ : Δ ≥ Δ₂ := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hΔ
  have hΔ_ge_Δ₃ : Δ ≥ Δ₃ := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hΔ
  have hΔ_ge_Δ₄ : Δ ≥ Δ₄ := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hΔ
  obtain ⟨α, ⟨hα_mem, hsumm_b, hsum0, hα_err⟩, _⟩ := h_opt Δ hΔ_ge_Δ₁
  have h_Δ3_exp : Δ ^ 3 * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
    have he := Real.pow_div_factorial_le_exp (2 * Real.pi * Δ) (by positivity) 3
    have hpi : (2 * Real.pi) ^ 3 / 6 ≥ 1 := by
      have h2 : 4 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      have h3 : 16 ≤ (2 * Real.pi) ^ 2 := by nlinarith
      nlinarith
    have h1 : Δ ^ 3 ≤ Real.exp (2 * Real.pi * Δ) := by
      calc Δ ^ 3 = 1 * Δ ^ 3 := (one_mul _).symm
        _ ≤ ((2 * Real.pi) ^ 3 / 6) * Δ ^ 3 := by gcongr
        _ = (2 * Real.pi * Δ) ^ 3 / Nat.factorial 3 := by norm_num; ring
        _ ≤ Real.exp (2 * Real.pi * Δ) := he
    rw [show (-2 * Real.pi * Δ : ℝ) = -(2 * Real.pi * Δ) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    exact h1.trans_eq (one_mul _).symm
  have h_Δ2_exp : Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by
    rw [le_div_iff₀ hΔ_pos]
    calc Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) * Δ = Δ ^ 3 * Real.exp (-2 * Real.pi * Δ) := by ring
      _ ≤ 1 := h_Δ3_exp
  have h_Δ1_exp : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by
    have h1 : Δ * Real.exp (-2 * Real.pi * Δ) ≤ Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) := by
      gcongr; nlinarith
    exact h1.trans h_Δ2_exp
  have hα_near : |α - α_star| ≤ δ_star / 2 := by
    have h1 : C_α * Δ * Real.exp (-2 * Real.pi * Δ) ≤ C_α / Δ := by
      calc C_α * Δ * Real.exp (-2 * Real.pi * Δ) = C_α * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
        _ ≤ C_α * (1 / Δ) := by gcongr
        _ = C_α / Δ := by ring
    have h2 : 2 * C_α / δ_star ≤ Δ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΔ |>.trans' (by linarith)
    have h3 : C_α / Δ ≤ δ_star / 2 := by
      rw [div_le_iff₀ hΔ_pos]
      rw [div_le_iff₀ hδ_star] at h2
      linarith
    exact hα_err.trans (h1.trans h3)
  obtain ⟨hM_type, hM_re⟩ := majorantEntire_props θ Δ α hΔ_ge_1 hα_mem hsumm_b
  obtain ⟨h_sup, h_int_M, h_L1⟩ := h_sup_L1 Δ α hΔ_ge_Δ₃ hα_mem hα_near hsumm_b hsum0
  have h_int_diff : Integrable (fun x : ℝ => majorantM θ Δ α x - kernelK θ x) :=
    h_int_M.sub (kernelK_integrable_sl θ)
  have h_ge_K : ∀ x : ℝ, x ≠ 0 → majorantM θ Δ α x ≥ kernelK θ x := by
    intro x hx
    have hy_ne : Δ * x ≠ 0 := mul_ne_zero hΔ_pos.ne' hx
    have h_res : rescaledF θ Δ (Δ * x) = kernelK θ x := by
      unfold rescaledF; congr 1; field_simp [hΔ_pos.ne']
    have h_diff := h_diff_bd Δ α hΔ_ge_Δ₂ hα_mem hα_near hsumm_b hsum0
    unfold majorantM
    rcases lt_or_ge |Δ * x| 1 with hy1 | hy1
    · have hd1 := (abs_le.mp (h_diff.1 (Δ * x) (abs_pos.mpr hy_ne) hy1)).1
      rw [h_res] at hd1
      have hj := hJ_small (Δ * x) (abs_pos.mpr hy_ne) hy1.le
      have h_err_le : C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) ≤ c'_J := by
        have h_1 : Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star| ≤ (1 + C_α) / Δ := by
          have h1 : |α - α_star| ≤ C_α / Δ := by
            calc |α - α_star| ≤ C_α * Δ * Real.exp (-2 * Real.pi * Δ) := hα_err
              _ = C_α * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
              _ ≤ C_α * (1 / Δ) := by gcongr
              _ = C_α / Δ := by ring
          linarith [show (1 : ℝ) / Δ + C_α / Δ = (1 + C_α) / Δ by ring]
        have h_2' : C_err1 * (1 + C_α) / c'_J + 1 ≤ Δ :=
          le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hΔ
        have h_2 : C_err1 * (1 + C_α) / c'_J ≤ Δ := by linarith
        calc C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|)
            ≤ C_err1 * ((1 + C_α) / Δ) := by gcongr
          _ = C_err1 * (1 + C_α) / Δ := by ring
          _ ≤ c'_J := by rw [div_le_iff₀ hΔ_pos]; rw [div_le_iff₀ hc'_J] at h_2; linarith
      have h_sin_nn : 0 ≤ Real.sin (Real.pi * (Δ * x - α)) ^ 2 := sq_nonneg _
      have h_log_nn : 0 ≤ Real.log (1 / |Δ * x|) := Real.log_nonneg ((one_le_div (abs_pos.mpr hy_ne)).mpr hy1.le)
      have h_err_mul : C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) * (1 + Real.log (1 / |Δ * x|)) ≤
          limitingJ (Δ * x) θ := by nlinarith
      linarith [mul_le_mul_of_nonneg_left h_err_mul h_sin_nn]
    · have hd2 := (abs_le.mp (h_diff.2 (Δ * x) hy1)).1
      rw [h_res] at hd2
      have hj := hJ_all (Δ * x) hy_ne
      have hj2 : (c_J / 2) / (Δ * x) ^ 2 ≤ limitingJ (Δ * x) θ := by
        have h_1y : 1 + (Δ * x) ^ 2 ≤ 2 * (Δ * x) ^ 2 := by rw [← sq_abs (Δ * x)]; nlinarith
        calc (c_J / 2) / (Δ * x) ^ 2 = c_J / (2 * (Δ * x) ^ 2) := by ring
          _ ≤ c_J / (1 + (Δ * x) ^ 2) := div_le_div_of_nonneg_left hc_J.le (by positivity) h_1y
          _ ≤ limitingJ (Δ * x) θ := hj
      have h_err_le : C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) ≤ c_J / 2 := by
        have h_1 : Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star| ≤ (1 + C_α) / Δ := by
          have h1 : |α - α_star| ≤ C_α / Δ := by
            calc |α - α_star| ≤ C_α * Δ * Real.exp (-2 * Real.pi * Δ) := hα_err
              _ = C_α * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
              _ ≤ C_α * (1 / Δ) := by gcongr
              _ = C_α / Δ := by ring
          linarith [show (1 : ℝ) / Δ + C_α / Δ = (1 + C_α) / Δ by ring]
        have h_2' : C_err1 * (1 + C_α) / (c_J / 2) + 1 ≤ Δ :=
          le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hΔ
        have h_2 : C_err1 * (1 + C_α) / (c_J / 2) ≤ Δ := by linarith
        calc C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star|)
            ≤ C_err1 * ((1 + C_α) / Δ) := by gcongr
          _ = C_err1 * (1 + C_α) / Δ := by ring
          _ ≤ c_J / 2 := by rw [div_le_iff₀ hΔ_pos]; rw [div_le_iff₀ (by positivity)] at h_2; linarith
      have h_sin_nn : 0 ≤ Real.sin (Real.pi * (Δ * x - α)) ^ 2 := sq_nonneg _
      have h_y2_pos : 0 ≤ 1 / (Δ * x) ^ 2 := by positivity
      have h_div_le : C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) / (Δ * x) ^ 2 ≤ (c_J / 2) / (Δ * x) ^ 2 :=
        div_le_div_of_nonneg_right h_err_le (sq_nonneg _)
      nlinarith
  have h_excess : |(∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) - 2 * envelopeC θ / Δ| ≤
      C_err * Real.exp (-2 * Real.pi * Δ) := by
    have h_sup_ex : ∃ C > 0, ∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x - 0| ≤ C := by
      refine ⟨C_sup * Real.log Δ, mul_pos hC_sup (Real.log_pos (by linarith [hΔ_ge_Δ₃])), fun x => by simpa using h_sup x⟩
    have h_vaaler_eq := vaaler_integral_eq_tsum θ Δ α hθ hΔ_ge_1 hα_mem hsumm_b hsum0 h_int_M
      ⟨C_sup * Real.log Δ, mul_pos hC_sup (Real.log_pos (by linarith [hΔ_ge_Δ₃])), h_sup⟩
    have h_scale_M : ∫ x : ℝ, majorantM θ Δ α x = (1 / Δ) * ∫ y : ℝ, vaalerInterpolant θ Δ α y := by
      unfold majorantM
      let fV : ℝ → ℝ := vaalerInterpolant θ Δ α
      have hfV_int : Integrable fV := by
        have h_eq : fV = fun y : ℝ => majorantM θ Δ α (y / Δ) := by
          ext y; dsimp only [fV, majorantM]; congr 1; field_simp [hΔ_pos.ne']
        rw [h_eq]; exact h_int_M.comp_div hΔ_pos.ne'
      have hfVc_int : Integrable (fun x : ℝ => fV (Δ * x)) := h_int_M
      have h_pos_int : ∫ x in Set.Ioi (0 : ℝ), fV (Δ * x) = (1 / Δ) * ∫ y in Set.Ioi (0 : ℝ), fV y := by
        have h := MeasureTheory.integral_comp_mul_left_Ioi fV (0 : ℝ) hΔ_pos
        rw [mul_zero, smul_eq_mul, inv_eq_one_div] at h
        exact h
      have h_neg_int : ∫ x in Set.Iio (0 : ℝ), fV (Δ * x) = (1 / Δ) * ∫ y in Set.Iio (0 : ℝ), fV y := by
        have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
        have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio (0 : ℝ) = Set.Ioi 0 := by
          ext x; simp only [Set.mem_preimage, Homeomorph.coe_neg, Set.mem_Iio, Set.mem_Ioi, neg_lt_zero]
        have h1 : ∫ x in Set.Iio (0 : ℝ), fV (Δ * x) = ∫ x in Set.Ioi (0 : ℝ), fV (-(Δ * x)) := by
          rw [← (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb (fun x => fV (Δ * x)) (Set.Iio 0)]
          have h_pre' : Neg.neg ⁻¹' Set.Iio (0 : ℝ) = Set.Ioi 0 := h_pre
          rw [h_pre']; simp only [Homeomorph.coe_neg, mul_neg]
        have h2 : ∫ y in Set.Iio (0 : ℝ), fV y = ∫ y in Set.Ioi (0 : ℝ), fV (-y) := by
          rw [← (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb fV (Set.Iio 0)]
          have h_pre' : Neg.neg ⁻¹' Set.Iio (0 : ℝ) = Set.Ioi 0 := h_pre
          rw [h_pre']
        have h3 := MeasureTheory.integral_comp_mul_left_Ioi (fun y : ℝ => fV (-y)) (0 : ℝ) hΔ_pos
        rw [mul_zero, smul_eq_mul, inv_eq_one_div] at h3
        rw [h1, h2, ← h3]
      have h_split1 : ∫ x : ℝ, fV (Δ * x) = (∫ x in Set.Iio (0 : ℝ), fV (Δ * x)) + ∫ x in Set.Ioi (0 : ℝ), fV (Δ * x) := by
        rw [← integral_Ici_eq_integral_Ioi, ← setIntegral_union (Set.disjoint_iff.mpr fun x ⟨h1, h2⟩ => by linarith [h1.out, h2.out])
          measurableSet_Ici hfVc_int.integrableOn hfVc_int.integrableOn, Set.Iio_union_Ici, setIntegral_univ]
      have h_split2 : ∫ y : ℝ, fV y = (∫ y in Set.Iio (0 : ℝ), fV y) + ∫ y in Set.Ioi (0 : ℝ), fV y := by
        rw [← integral_Ici_eq_integral_Ioi, ← setIntegral_union (Set.disjoint_iff.mpr fun x ⟨h1, h2⟩ => by linarith [h1.out, h2.out])
          measurableSet_Ici hfV_int.integrableOn hfV_int.integrableOn, Set.Iio_union_Ici, setIntegral_univ]
      rw [show (fun x : ℝ => vaalerInterpolant θ Δ α (Δ * x)) = fun x : ℝ => fV (Δ * x) by rfl,
        h_split1, h_neg_int, h_pos_int, h_split2]
      ring
    have h_diff_eq : ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x) =
        (∫ x : ℝ, majorantM θ Δ α x) - (∫ x : ℝ, kernelK θ x) :=
      integral_sub h_int_M (kernelK_integrable_sl θ)
    rw [h_diff_eq, h_scale_M, h_vaaler_eq, kernelK_integral_eq θ]
    have h_ev := h_tsum_eval Δ α hΔ_ge_Δ₄ hα_mem hα_near
    have h_id : (1 / Δ) * (∑' n : ℤ, rescaledF θ Δ (n + α)) - (-Real.pi * Real.cos θ) - 2 * envelopeC θ / Δ =
        (1 / Δ) * ((∑' n : ℤ, rescaledF θ Δ (n + α)) - (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)) := by
      field_simp [hΔ_pos.ne']; ring
    rw [h_id, abs_mul, abs_of_pos (by positivity : 0 < 1 / Δ)]
    calc (1 / Δ) * |(∑' n : ℤ, rescaledF θ Δ (n + α)) - (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)|
        ≤ (1 / Δ) * (C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|)) :=
          mul_le_mul_of_nonneg_left h_ev (by positivity)
      _ ≤ (1 / Δ) * (C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + C_α * Δ * Real.exp (-2 * Real.pi * Δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl hα_err) hC_eval.le) (by positivity)
      _ = C_err * Real.exp (-2 * Real.pi * Δ) := by
          dsimp only [C_err]; field_simp [hΔ_pos.ne']
  exact ⟨α, majorantEntire θ Δ α, hα_mem, hM_type, hM_re, h_int_diff, h_sup, h_L1, h_ge_K, h_excess⟩

end PolarEvaluation
