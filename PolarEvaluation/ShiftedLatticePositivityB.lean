import PolarEvaluation.ShiftedLatticePositivityA

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

lemma cosh_fourier_eq {θ x : ℝ} (hθ : |θ| < Real.pi / 2) (hx : x ≠ 0) :
    ∫ ω : ℝ, (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * x) =
      1 / Complex.cos (θ + Complex.I * x / 2) := by
  have hδ_pos : 0 < Real.pi - 2 * |θ| := by linarith [(abs_lt.mp hθ).1, (abs_lt.mp hθ).2]
  have h_series_pos : ∀ ω : ℝ, 0 < ω →
      1 / Real.cosh (Real.pi * ω) =
        2 * ∑' k : ℕ, (Real.exp (-((4 * k + 1 : ℕ) : ℝ) * Real.pi * ω) -
          Real.exp (-((4 * k + 3 : ℕ) : ℝ) * Real.pi * ω)) := by
    intro ω hω
    have hr : Real.exp (-4 * Real.pi * ω) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    have hr_nonneg : 0 ≤ Real.exp (-4 * Real.pi * ω) := (Real.exp_pos _).le
    have hgeom : (∑' k : ℕ, Real.exp (-4 * Real.pi * ω) ^ k) =
        (1 - Real.exp (-4 * Real.pi * ω))⁻¹ := tsum_geometric_of_lt_one hr_nonneg hr
    have h_eq : ∀ k : ℕ, Real.exp (-((4 * k + 1 : ℕ) : ℝ) * Real.pi * ω) -
        Real.exp (-((4 * k + 3 : ℕ) : ℝ) * Real.pi * ω) =
        (Real.exp (-Real.pi * ω) - Real.exp (-3 * Real.pi * ω)) * Real.exp (-4 * Real.pi * ω) ^ k := by
      intro k
      rw [← Real.exp_nat_mul]
      have h1 : -((4 * k + 1 : ℕ) : ℝ) * Real.pi * ω = -Real.pi * ω + (k : ℝ) * (-4 * Real.pi * ω) := by
        push_cast; ring
      have h2 : -((4 * k + 3 : ℕ) : ℝ) * Real.pi * ω = -3 * Real.pi * ω + (k : ℝ) * (-4 * Real.pi * ω) := by
        push_cast; ring
      rw [h1, h2, Real.exp_add, Real.exp_add]; ring
    simp_rw [h_eq, tsum_mul_left, hgeom]
    rw [Real.cosh_eq]
    have h1m : 1 - Real.exp (-4 * Real.pi * ω) =
        (1 + Real.exp (-2 * Real.pi * ω)) * (1 - Real.exp (-2 * Real.pi * ω)) := by
      have : Real.exp (-4 * Real.pi * ω) = Real.exp (-2 * Real.pi * ω) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [this]; ring
    have h_ne1 : 1 - Real.exp (-2 * Real.pi * ω) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])))
    have h_ne2 : 1 + Real.exp (-2 * Real.pi * ω) ≠ 0 := by positivity
    have h_e1 : Real.exp (-3 * Real.pi * ω) = Real.exp (-Real.pi * ω) * Real.exp (-2 * Real.pi * ω) := by
      rw [← Real.exp_add]; ring_nf
    have h_e2 : Real.exp (Real.pi * ω) * Real.exp (-Real.pi * ω) = 1 := by
      rw [← Real.exp_add]; simp
    have h_e3 : Real.exp (Real.pi * ω) * Real.exp (-2 * Real.pi * ω) = Real.exp (-Real.pi * ω) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1m, h_e1]
    field_simp [h_ne1, h_ne2, (Real.cosh_pos _).ne']
    nlinarith
  have h_int_exp_diff : ∀ (a b x' : ℝ), 0 < a → a < b →
      (∫ ω in Set.Ioi (0 : ℝ),
        ((Real.exp (-a * ω) - Real.exp (-b * ω) : ℝ) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
        1 / ((a : ℂ) + Complex.I * x') - 1 / ((b : ℂ) + Complex.I * x') := by
    intro a b x' ha hab
    have h_one : ∀ (c : ℝ), 0 < c →
        (∫ ω in Set.Ioi (0 : ℝ), (Real.exp (-c * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
          1 / ((c : ℂ) + Complex.I * x') := by
      intro c hc
      have h_eq : (fun ω : ℝ => (Real.exp (-c * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
          fun ω : ℝ => Complex.exp (-((c : ℂ) + Complex.I * x') * ω) := by
        ext ω; rw [← Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [h_eq]
      have h_re_neg : (-((c : ℂ) + Complex.I * x')).re < 0 := by simp [hc]
      exact integral_exp_mul_complex_Ioi h_re_neg 0 |>.trans (by simp; ring)
    have h_i1 : IntegrableOn (fun ω : ℝ => (Real.exp (-a * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) (Set.Ioi 0) := by
      have : (fun ω : ℝ => (Real.exp (-a * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
          fun ω : ℝ => Complex.exp (-((a : ℂ) + Complex.I * x') * ω) := by
        ext ω; rw [← Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; exact integrableOn_exp_mul_complex_Ioi (by simp [ha]) 0
    have h_i2 : IntegrableOn (fun ω : ℝ => (Real.exp (-b * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) (Set.Ioi 0) := by
      have : (fun ω : ℝ => (Real.exp (-b * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
          fun ω : ℝ => Complex.exp (-((b : ℂ) + Complex.I * x') * ω) := by
        ext ω; rw [← Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; exact integrableOn_exp_mul_complex_Ioi (by simp [lt_trans ha hab]) 0
    have h_sub_eq : (fun ω : ℝ => ((Real.exp (-a * ω) - Real.exp (-b * ω) : ℝ) : ℂ) * Complex.exp (-Complex.I * ω * x')) =
        fun ω : ℝ => (Real.exp (-a * ω) : ℂ) * Complex.exp (-Complex.I * ω * x') -
          (Real.exp (-b * ω) : ℂ) * Complex.exp (-Complex.I * ω * x') := by
      ext ω; push_cast; ring
    rw [h_sub_eq, MeasureTheory.integral_sub h_i1 h_i2, h_one a ha, h_one b (lt_trans ha hab)]
  have h_pos_part : ∀ (θ' x' : ℝ), |θ'| < Real.pi / 2 →
      (∫ ω in Set.Ioi (0 : ℝ),
        (Real.exp (-2 * θ' * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * x')) =
        ∑' k : ℕ, (2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x') -
          2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x')) := by
    intro θ' x' hθ'
    have hδ' : 0 < Real.pi - 2 * |θ'| := by linarith [(abs_lt.mp hθ').1, (abs_lt.mp hθ').2]
    let f : ℕ → ℝ → ℂ := fun k ω =>
      2 * ((Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ω * x')
    have hf_meas : ∀ k : ℕ, AEStronglyMeasurable (f k) (volume.restrict (Set.Ioi 0)) :=
      fun k => Continuous.aestronglyMeasurable (by fun_prop)
    have h_a_lb : ∀ k : ℕ, (k + 1 : ℝ) * (Real.pi - 2 * |θ'|) ≤ ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
      intro k
      have h1 : -2 * |θ'| ≤ 2 * θ' := by linarith [neg_le_abs θ']
      have h2 : (k + 1 : ℝ) * (Real.pi - 2 * |θ'|) ≤ ((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * |θ'| := by
        have hk : (k : ℝ) * (Real.pi - 2 * |θ'|) ≤ 4 * (k : ℝ) * Real.pi := by
          nlinarith [abs_nonneg θ', Real.pi_pos]
        push_cast; linarith
      linarith
    have h_lintegral : ∀ k : ℕ, ∫⁻ ω in Set.Ioi (0 : ℝ), ‖f k ω‖₊ =
        ENNReal.ofReal (2 * (1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') -
          1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ'))) := by
      intro k
      have ha_pos : 0 < ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' :=
        lt_of_lt_of_le (mul_pos (by positivity) hδ') (h_a_lb k)
      have hb_pos : 0 < ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by push_cast; linarith [Real.pi_pos]
      have hab : ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' < ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
        push_cast; linarith [Real.pi_pos]
      have h_norm_eq : Set.EqOn (fun ω : ℝ => (‖f k ω‖ : ℝ))
          (fun ω : ℝ => 2 * (Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω))) (Set.Ioi 0) := by
        intro ω (hω : 0 < ω)
        dsimp only [f]
        have hexp_n : ‖Complex.exp (-Complex.I * ω * x')‖ = 1 := by
          rw [show -Complex.I * (ω : ℂ) * x' = ((-ω * x' : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        have hdiff_nonneg : 0 ≤ Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) := by
          have : -(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω ≤
              -(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω := by nlinarith [hω.le]
          linarith [Real.exp_le_exp.mpr this]
        rw [norm_mul, hexp_n, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hdiff_nonneg]
      have h_int_norm : IntegrableOn (fun ω : ℝ => 2 * (Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω))) (Set.Ioi 0) := by
        have h1 : IntegrableOn (fun ω : ℝ => Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun ω : ℝ => Complex.exp (((-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') : ℝ) : ℂ) * ω)) (Set.Ioi 0) :=
            integrableOn_exp_mul_complex_Ioi (by rw [Complex.ofReal_re]; linarith) 0
          refine hc.norm.congr (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h2 : IntegrableOn (fun ω : ℝ => Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun ω : ℝ => Complex.exp (((-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') : ℝ) : ℂ) * ω)) (Set.Ioi 0) :=
            integrableOn_exp_mul_complex_Ioi (by rw [Complex.ofReal_re]; linarith) 0
          refine hc.norm.congr (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (h1.sub h2).const_mul 2
      have h_int_val : (∫ ω in Set.Ioi (0 : ℝ), 2 * (Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω))) =
          2 * (1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') -
            1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ')) := by
        have h_c := h_int_exp_diff (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ')
          (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') 0 ha_pos hab
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, add_zero] at h_c
        have h_c' : ((∫ ω in Set.Ioi (0 : ℝ), (Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω))) : ℂ) =
            ((1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') -
              1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') : ℝ) : ℂ) := by
          trans (∫ ω in Set.Ioi (0 : ℝ), ((Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
            Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) : ℝ) : ℂ))
          · exact (integral_ofReal).symm
          · push_cast at h_c ⊢; exact h_c
        rw [MeasureTheory.integral_const_mul, Complex.ofReal_injective h_c']
      have hf_int : IntegrableOn (f k) (Set.Ioi 0) := by
        refine h_int_norm.mono' (hf_meas k) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω hω
        rw [h_norm_eq hω]
      rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_nnnorm hf_int,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_norm_eq, h_int_val]
    have h_tsum_ne_top : (∑' k : ℕ, ∫⁻ ω in Set.Ioi (0 : ℝ), ‖f k ω‖₊) ≠ ⊤ := by
      simp_rw [h_lintegral]
      have hM_summ : Summable (fun k : ℕ => 2 * (1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') -
          1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ'))) := by
        refine (summable_one_div_sq_nat.mul_left (4 * Real.pi / (Real.pi - 2 * |θ'|) ^ 2)).of_nonneg_of_le
          (fun k => ?_) (fun k => ?_)
        · have ha := lt_of_lt_of_le (mul_pos (by positivity) hδ') (h_a_lb k)
          have hb : ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' ≤ ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
            push_cast; linarith [Real.pi_pos]
          have : 1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') ≤ 1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') :=
            div_le_div_of_nonneg_left zero_le_one ha hb
          linarith
        · have ha := lt_of_lt_of_le (mul_pos (by positivity) hδ') (h_a_lb k)
          have hb : ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' ≤ ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
            push_cast; linarith [Real.pi_pos]
          have heq : 2 * (1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') -
              1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ')) =
              4 * Real.pi / ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') *
                (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ')) := by
            have ha' : (4 * (k : ℝ) + 1) * Real.pi + 2 * θ' ≠ 0 := by push_cast at ha; exact ha.ne'
            have hb' : (4 * (k : ℝ) + 3) * Real.pi + 2 * θ' ≠ 0 := by push_cast at hb; linarith
            push_cast; rw [div_sub_div _ _ ha' hb']; ring
          rw [heq]
          have hden : ((k + 1 : ℝ) * (Real.pi - 2 * |θ'|)) ^ 2 ≤
              (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') := by
            rw [sq]; exact mul_le_mul (h_a_lb k) ((h_a_lb k).trans hb) (by positivity) ha.le
          calc 4 * Real.pi / _ ≤ 4 * Real.pi / ((k + 1 : ℝ) * (Real.pi - 2 * |θ'|)) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hden
            _ = (4 * Real.pi / (Real.pi - 2 * |θ'|) ^ 2) * (1 / (k + 1 : ℝ) ^ 2) := by
              rw [mul_pow, div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) hM_summ]
      · exact ENNReal.ofReal_ne_top
      · have ha := lt_of_lt_of_le (mul_pos (by positivity) hδ') (h_a_lb k)
        have hb : ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' ≤ ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
          push_cast; linarith [Real.pi_pos]
        have : 1 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') ≤ 1 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') :=
          div_le_div_of_nonneg_left zero_le_one ha hb
        linarith
    have h_fub := MeasureTheory.integral_tsum hf_meas h_tsum_ne_top
    have h_congr : Set.EqOn (fun ω : ℝ =>
        (Real.exp (-2 * θ' * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * x'))
        (fun ω : ℝ => ∑' k : ℕ, f k ω) (Set.Ioi 0) := by
      intro ω hω
      rw [← Complex.ofReal_div, div_eq_mul_one_div (Real.exp (-2 * θ' * ω)), h_series_pos ω hω]
      have h_eq_k : (fun k : ℕ => f k ω) = fun k : ℕ =>
          (2 * (Real.exp (-2 * θ' * ω) : ℂ) * Complex.exp (-Complex.I * ω * x')) *
            ((Real.exp (-((4 * k + 1 : ℕ) : ℝ) * Real.pi * ω) -
              Real.exp (-((4 * k + 3 : ℕ) : ℝ) * Real.pi * ω) : ℝ) : ℂ) := by
        ext k; dsimp only [f]
        have h1 : -(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω =
            -2 * θ' * ω + -((4 * k + 1 : ℕ) : ℝ) * Real.pi * ω := by ring
        have h2 : -(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω =
            -2 * θ' * ω + -((4 * k + 3 : ℕ) : ℝ) * Real.pi * ω := by ring
        rw [h1, h2, Real.exp_add, Real.exp_add]; push_cast; ring
      rw [h_eq_k, tsum_mul_left, ← Complex.ofReal_tsum]; push_cast; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_congr, h_fub]
    congr 1; ext k
    have ha_pos : 0 < ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' :=
      lt_of_lt_of_le (mul_pos (by positivity) hδ') (h_a_lb k)
    have hab : ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' < ((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' := by
      push_cast; linarith [Real.pi_pos]
    have h_f_eq : (fun ω : ℝ => f k ω) = fun ω : ℝ =>
        (2 : ℂ) * (((Real.exp (-(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) -
          Real.exp (-(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') * ω) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ω * x')) := by
      ext ω; dsimp only [f]; ring
    rw [h_f_eq, MeasureTheory.integral_const_mul,
      h_int_exp_diff (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ')
        (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ') x' ha_pos hab]
    push_cast; ring
  let G : ℝ → ℂ := fun ω => (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * x)
  have h_exp_p : IntegrableOn (fun ω : ℝ => Real.exp (-(Real.pi - 2 * |θ|) * ω)) (Set.Ioi 0) := by
    have hc : IntegrableOn (fun ω : ℝ => Complex.exp (((-(Real.pi - 2 * |θ|) : ℝ) : ℂ) * ω)) (Set.Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by rw [Complex.ofReal_re]; linarith [hδ_pos]) 0
    refine hc.norm.congr (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h_cont_G : Continuous G := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) ?_
    · exact Continuous.div (Real.continuous_exp.comp (continuous_const.mul continuous_id))
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) (fun ω => (Real.cosh_pos _).ne')
    · exact Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have h_int_Ioi : IntegrableOn G (Set.Ioi 0) := by
    refine (h_exp_p.const_mul 2).mono' h_cont_G.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
    dsimp only [G]
    have hexp_n : ‖Complex.exp (-Complex.I * ω * x)‖ = 1 := by
      rw [show -Complex.I * (ω : ℂ) * x = ((-ω * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_n, mul_one, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]
    have hch : Real.exp (Real.pi * ω) / 2 ≤ Real.cosh (Real.pi * ω) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * ω))]
    have h1 : Real.exp (-2 * θ * ω) ≤ Real.exp (2 * |θ| * ω) := by
      gcongr; nlinarith [neg_le_abs θ, hω.le]
    calc Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)
        ≤ Real.exp (2 * |θ| * ω) / (Real.exp (Real.pi * ω) / 2) := by
          gcongr; exact div_pos (Real.exp_pos _) two_pos
      _ = 2 * Real.exp (-(Real.pi - 2 * |θ|) * ω) := by
          rw [show -(Real.pi - 2 * |θ|) * ω = 2 * |θ| * ω - Real.pi * ω by ring, Real.exp_sub]; ring
  have h_int_neg_Ioi : IntegrableOn (fun ω : ℝ => G (-ω)) (Set.Ioi 0) := by
    refine (h_exp_p.const_mul 2).mono' (h_cont_G.comp continuous_neg).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
    dsimp only [G]
    have hexp_n : ‖Complex.exp (-Complex.I * (-ω : ℝ) * x)‖ = 1 := by
      rw [show -Complex.I * ((-ω : ℝ) : ℂ) * x = ((ω * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_n, mul_one, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]
    have hch : Real.exp (Real.pi * ω) / 2 ≤ Real.cosh (Real.pi * ω) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * ω))]
    have h1 : Real.exp (-2 * θ * (-ω)) ≤ Real.exp (2 * |θ| * ω) := by
      gcongr; nlinarith [le_abs_self θ, hω.le]
    calc Real.exp (-2 * θ * (-ω)) / Real.cosh (Real.pi * (-ω))
        = Real.exp (-2 * θ * (-ω)) / Real.cosh (Real.pi * ω) := by rw [mul_neg, Real.cosh_neg]
      _ ≤ Real.exp (2 * |θ| * ω) / (Real.exp (Real.pi * ω) / 2) := by
          gcongr; exact div_pos (Real.exp_pos _) two_pos
      _ = 2 * Real.exp (-(Real.pi - 2 * |θ|) * ω) := by
          rw [show -(Real.pi - 2 * |θ|) * ω = 2 * |θ| * ω - Real.pi * ω by ring, Real.exp_sub]; ring
  have h_int_Iio : IntegrableOn G (Set.Iio 0) := by
    have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
    have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by
      ext ω; simp [Set.mem_Iio, Set.mem_Ioi]
    have h1 := (Measure.measurePreserving_neg volume).integrableOn_comp_preimage h_emb (s := Set.Iio 0)
    rw [h_pre] at h1
    exact h1.mp h_int_neg_Ioi
  have h_int_Iic : IntegrableOn G (Set.Iic 0) := h_int_Iio.congr_set_ae Iio_ae_eq_Iic.symm
  have h_split : (∫ ω : ℝ, G ω) = (∫ ω in Set.Ioi (0 : ℝ), G ω) + (∫ ω in Set.Ioi (0 : ℝ), G (-ω)) := by
    have h_union : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := Set.Iic_union_Ioi
    have h_disj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi 0) := Set.Iic_disjoint_Ioi le_rfl
    have h_univ : (∫ ω : ℝ, G ω) = (∫ ω in Set.Iic (0 : ℝ), G ω) + (∫ ω in Set.Ioi (0 : ℝ), G ω) := by
      rw [← MeasureTheory.setIntegral_univ, ← h_union,
        MeasureTheory.setIntegral_union h_disj measurableSet_Ioi h_int_Iic h_int_Ioi]
    have h_Iic_Iio : (∫ ω in Set.Iic (0 : ℝ), G ω) = ∫ ω in Set.Iio (0 : ℝ), G ω :=
      MeasureTheory.integral_Iic_eq_integral_Iio
    have h_Iio_Ioi : (∫ ω in Set.Iio (0 : ℝ), G ω) = ∫ ω in Set.Ioi (0 : ℝ), G (-ω) := by
      have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
      have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by
        ext ω; simp [Set.mem_Iio, Set.mem_Ioi]
      have h_eq := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb G (Set.Iio 0)
      change ∫ x in (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0, G (-x) = ∫ y in Set.Iio 0, G y at h_eq
      rw [h_pre] at h_eq
      exact h_eq.symm
    rw [h_univ, h_Iic_Iio, h_Iio_Ioi, add_comm]
  have hG_neg_eq : (fun ω : ℝ => G (-ω)) = fun ω : ℝ =>
      (Real.exp (-2 * (-θ) * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * ((-x : ℝ) : ℂ)) := by
    ext ω; dsimp only [G]; rw [mul_neg (Real.pi), Real.cosh_neg]; push_cast; ring_nf
  have h_main : (∫ ω : ℝ, G ω) =
      ∑' k : ℕ,
        ((2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) -
          2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x)) +
         (2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ - Complex.I * x) -
          2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi - 2 * θ - Complex.I * x))) := by
    rw [h_split, hG_neg_eq, h_pos_part θ x hθ, h_pos_part (-θ) (-x) (by rwa [abs_neg])]
    have hs1 : Summable (fun k : ℕ => 2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) -
        2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x)) := by
      refine (summable_one_div_sq_nat.mul_left (4 * Real.pi / (Real.pi - 2 * |θ|) ^ 2)).of_norm_bounded fun k => ?_
      have h1 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ := by
        have : -2 * |θ| ≤ 2 * θ := by linarith [neg_le_abs θ]
        have : (k : ℝ) * (Real.pi - 2 * |θ|) ≤ 4 * (k : ℝ) * Real.pi := by nlinarith [abs_nonneg θ, Real.pi_pos]
        push_cast; linarith
      have ha_pos : 0 < ((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ := lt_of_lt_of_le (mul_pos (by positivity) hδ_pos) h1
      have hne1 : (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; push_cast at ha_pos; linarith
      have hne2 : (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; push_cast at ha_pos; linarith [Real.pi_pos]
      have heq : 2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) -
          2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) =
          4 * Real.pi / ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) *
            (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x)) := by
        rw [div_sub_div _ _ hne1 hne2]; congr 1; push_cast; ring
      have hnum : ‖(4 : ℂ) * Real.pi‖ = 4 * Real.pi := by
        rw [show (4 : ℂ) * Real.pi = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [heq, norm_div, hnum, norm_mul]
      have h_n1 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ‖(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x‖ := by
        have := Complex.abs_re_le_norm ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x)
        simp at this; push_cast at h1 this ⊢; linarith [le_abs_self ((4 * (k : ℝ) + 1) * Real.pi + 2 * θ)]
      have h_n2 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ‖(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x‖ := by
        have := Complex.abs_re_le_norm ((((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x)
        simp at this; push_cast at h1 this ⊢; linarith [le_abs_self ((4 * (k : ℝ) + 3) * Real.pi + 2 * θ), Real.pi_pos]
      have hden : ((k + 1 : ℝ) * (Real.pi - 2 * |θ|)) ^ 2 ≤
          ‖(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x‖ *
          ‖(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ : ℂ) + Complex.I * x‖ := by
        rw [sq]; exact mul_le_mul h_n1 h_n2 (by positivity) (norm_nonneg _)
      calc 4 * Real.pi / _ ≤ 4 * Real.pi / ((k + 1 : ℝ) * (Real.pi - 2 * |θ|)) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = (4 * Real.pi / (Real.pi - 2 * |θ|) ^ 2) * (1 / (k + 1 : ℝ) ^ 2) := by
            field_simp [hδ_pos.ne', (by positivity : (k : ℝ) + 1 ≠ 0)]
    have hs2 : Summable (fun k : ℕ => 2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x)) -
        2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x))) := by
      refine (summable_one_div_sq_nat.mul_left (4 * Real.pi / (Real.pi - 2 * |θ|) ^ 2)).of_norm_bounded fun k => ?_
      have h1 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ := by
        have : -2 * |θ| ≤ -2 * θ := by linarith [le_abs_self θ]
        have : (k : ℝ) * (Real.pi - 2 * |θ|) ≤ 4 * (k : ℝ) * Real.pi := by nlinarith [abs_nonneg θ, Real.pi_pos]
        push_cast; linarith
      have ha_pos : 0 < ((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ := lt_of_lt_of_le (mul_pos (by positivity) hδ_pos) h1
      have hne1 : (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x) ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; push_cast at ha_pos; linarith
      have hne2 : (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x) ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; push_cast at ha_pos; linarith [Real.pi_pos]
      have heq : 2 / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x)) -
          2 / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x)) =
          4 * Real.pi / ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x)) *
            (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) + Complex.I * (-x))) := by
        rw [div_sub_div _ _ hne1 hne2]; congr 1; push_cast; ring
      have hnum : ‖(4 : ℂ) * Real.pi‖ = 4 * Real.pi := by
        rw [show (4 : ℂ) * Real.pi = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [heq, norm_div, hnum, norm_mul]
      have h_n1 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ‖(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)‖ := by
        have h_re : ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)).re = (4 * (k : ℝ) + 1) * Real.pi - 2 * θ := by
          simp; push_cast; ring
        have := Complex.abs_re_le_norm ((((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x))
        rw [h_re] at this; push_cast at h1; linarith [le_abs_self ((4 * (k : ℝ) + 1) * Real.pi - 2 * θ)]
      have h_n2 : (k + 1 : ℝ) * (Real.pi - 2 * |θ|) ≤ ‖(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)‖ := by
        have h_re : ((((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)).re = (4 * (k : ℝ) + 3) * Real.pi - 2 * θ := by
          simp; push_cast; ring
        have := Complex.abs_re_le_norm ((((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x))
        rw [h_re] at this; push_cast at h1; linarith [le_abs_self ((4 * (k : ℝ) + 3) * Real.pi - 2 * θ), Real.pi_pos]
      have hden : ((k + 1 : ℝ) * (Real.pi - 2 * |θ|)) ^ 2 ≤
          ‖(((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)‖ *
          ‖(((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * (-θ) : ℂ) + Complex.I * (-x)‖ := by
        rw [sq]; exact mul_le_mul h_n1 h_n2 (by positivity) (norm_nonneg _)
      calc 4 * Real.pi / _ ≤ 4 * Real.pi / ((k + 1 : ℝ) * (Real.pi - 2 * |θ|)) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = (4 * Real.pi / (Real.pi - 2 * |θ|) ^ 2) * (1 / (k + 1 : ℝ) ^ 2) := by
            field_simp [hδ_pos.ne', (by positivity : (k : ℝ) + 1 ≠ 0)]
    rw [← Summable.tsum_add hs1 (by simpa only [Complex.ofReal_neg] using hs2)]
    congr 1; ext k; push_cast; ring
  have h_pi_eq := pi_div_cos_tsum_eq hθ hx
  have h_mul : (Real.pi : ℂ) * (∫ ω : ℝ, G ω) = (Real.pi : ℂ) / Complex.cos (θ + Complex.I * x / 2) := by
    rw [h_main, h_pi_eq, ← tsum_mul_left]
    congr 1; ext k; ring
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (h_mul.trans (div_eq_mul_one_div _ _))

lemma limitingJ_pos_of_pos {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : 0 < y) :
    0 < limitingJ y θ := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hδ_pos : 0 < Real.pi - 2 * |θ| := by linarith [(abs_lt.mp hθ).1, (abs_lt.mp hθ).2]
  let Ψ : ℝ → ℝ := fun s => (∫ v in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (Complex.I * s * v)).im
  have h_J_laplace : limitingJ y θ = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * y) * Ψ s := by
    have h_inv_lap : ∀ v : ℝ,
        cTheta θ v / ((y : ℂ) - Complex.I * v) =
          ∫ s in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (-((y : ℂ) - Complex.I * v) * s) := by
      intro v
      have h_re : (-((y : ℂ) - Complex.I * v)).re < 0 := by simp [hy]
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi h_re 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [neg_div_neg_eq, one_div]; ring
    have h_prod_int' : Integrable (fun p : ℝ × ℝ =>
        cTheta θ p.1 * Complex.exp (-((y : ℂ) - Complex.I * p.1) * p.2))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
      have h_e1 : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h_e2 : IntegrableOn (fun s : ℝ => Real.exp (-y * s)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun s : ℝ => Complex.exp ((-y : ℂ) * s)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp [hy]) 0
        refine hc.norm.congr (Eventually.of_forall fun s => ?_)
        dsimp only
        rw [show ((-y : ℂ) * s) = ((-y * s : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h_prod_r := (h_e1.const_mul (4 / Real.cos θ ^ 2)).mul_prod h_e2
      have h_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          cTheta θ p.1 * Complex.exp (-((y : ℂ) - Complex.I * p.1) * p.2))
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
        refine Continuous.aestronglyMeasurable ?_
        refine Continuous.mul ?_ (Complex.continuous_exp.comp (by fun_prop))
        refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun p => ?_)
        exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
      refine h_prod_r.mono' h_meas ?_
      rw [MeasureTheory.Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      rw [norm_mul, Complex.norm_exp]
      have h_re_exp : (-((y : ℂ) - Complex.I * p.1) * p.2).re = -y * p.2 := by simp
      rw [h_re_exp]
      exact mul_le_mul_of_nonneg_right (cTheta_norm_le hθ hp.1.le) (Real.exp_pos _).le
    have h_swap' := MeasureTheory.integral_integral_swap (f := fun (v s : ℝ) => cTheta θ v * Complex.exp (-((y : ℂ) - Complex.I * v) * s)) h_prod_int'
    have h_int_v : IntegrableOn (fun v : ℝ => cTheta θ v / ((y : ℂ) - Complex.I * v)) (Set.Ioi 0) := by
      refine (cTheta_integrableOn hθ).norm.const_mul (1 / y) |>.mono'
        (Continuous.aestronglyMeasurable ?_) ?_
      · refine Continuous.div ?_ (by fun_prop) (fun v => ?_)
        · refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
          exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
        · intro h0; have hre := congr_arg Complex.re h0; simp at hre; linarith
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        rw [norm_div]
        have hy_lb : y ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have := Complex.abs_re_le_norm ((y : ℂ) - Complex.I * v)
          simp at this; linarith [le_abs_self y]
        calc ‖cTheta θ v‖ / ‖(y : ℂ) - Complex.I * v‖ ≤ ‖cTheta θ v‖ / y :=
              div_le_div_of_nonneg_left (norm_nonneg _) hy hy_lb
          _ = 1 / y * ‖cTheta θ v‖ := by ring
    have h_J_im : limitingJ y θ = (∫ v in Set.Ioi (0 : ℝ), cTheta θ v / ((y : ℂ) - Complex.I * v)).im := by
      unfold limitingJ
      have h_eq : (fun v : ℝ => (Complex.exp (-Complex.I * θ) /
          (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im) =
          fun v => (cTheta θ v / ((y : ℂ) - Complex.I * v)).im := by
        ext v; dsimp only [cTheta]; rw [div_div]
      rw [h_eq]
      simpa only [Complex.imCLM_apply] using Complex.imCLM.integral_comp_comm h_int_v
    rw [h_J_im]
    have h_integrand_eq : ∀ s v : ℝ,
        cTheta θ v * Complex.exp (-((y : ℂ) - Complex.I * v) * s) =
        ((Real.exp (-s * y) : ℝ) : ℂ) * (cTheta θ v * Complex.exp (Complex.I * s * v)) := by
      intro s v
      rw [Complex.ofReal_exp,
        show -((y : ℂ) - Complex.I * v) * s = ((-s * y : ℝ) : ℂ) + Complex.I * s * v by push_cast; ring,
        Complex.exp_add]
      ring
    have h_eq1 : (∫ v in Set.Ioi (0 : ℝ), cTheta θ v / ((y : ℂ) - Complex.I * v)) =
        ∫ s in Set.Ioi (0 : ℝ), ((Real.exp (-s * y) : ℝ) : ℂ) *
          (∫ v in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (Complex.I * s * v)) := by
      simp_rw [h_inv_lap]
      rw [h_swap']
      congr 1; ext s
      simp_rw [h_integrand_eq s]
      exact MeasureTheory.integral_const_mul _ _
    have h_s_int : IntegrableOn (fun s : ℝ => ((Real.exp (-s * y) : ℝ) : ℂ) *
        (∫ v in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (Complex.I * s * v))) (Set.Ioi 0) := by
      have h_prod2 := h_prod_int'.integral_prod_right
      refine h_prod2.congr (Eventually.of_forall fun s => ?_)
      dsimp only
      simp_rw [h_integrand_eq s]
      exact MeasureTheory.integral_const_mul _ _
    rw [h_eq1]
    change Complex.imCLM _ = _
    rw [← Complex.imCLM.integral_comp_comm h_s_int]
    dsimp only [Complex.imCLM_apply]
    congr 1; ext s
    rw [Complex.im_ofReal_mul]
  have h_Psi_pos : ∀ s : ℝ, 0 < s → 0 < Ψ s := by
    intro s hs
    have h_ibp : (∫ v in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (Complex.I * s * v)) =
        uTheta θ 0 + Complex.I * s * (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)) := by
      let W : ℝ → ℂ := fun v => -uTheta θ v * Complex.exp (Complex.I * s * v)
      have hW_deriv : ∀ v ∈ Set.Ici (0 : ℝ),
          HasDerivAt W (cTheta θ v * Complex.exp (Complex.I * s * v) -
            Complex.I * s * (uTheta θ v * Complex.exp (Complex.I * s * v))) v := by
        intro v _
        have hd1 : HasDerivAt (fun t => -uTheta θ t) (cTheta θ v) v := uTheta_deriv hθ
        have hd2 : HasDerivAt (fun (t : ℝ) => Complex.exp (Complex.I * s * t))
            (Complex.exp (Complex.I * s * v) * (Complex.I * s)) v := by
          have h := (hasDerivAt_id v).ofReal_comp.const_mul (Complex.I * s)
          simpa using h.cexp
        refine (hd1.mul hd2).congr_deriv ?_
        ring
      have h1 : IntegrableOn (fun v : ℝ => cTheta θ v * Complex.exp (Complex.I * s * v)) (Set.Ioi 0) := by
        refine (cTheta_integrableOn hθ).norm.mono' (Continuous.aestronglyMeasurable ?_) ?_
        · refine Continuous.mul ?_ (Complex.continuous_exp.comp (by fun_prop))
          refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
          exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
          have hn : ‖Complex.exp (Complex.I * s * v)‖ = 1 := by
            rw [show Complex.I * (s : ℂ) * v = ((s * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, hn, mul_one]
      have h2 : IntegrableOn (fun v : ℝ => uTheta θ v * Complex.exp (Complex.I * s * v)) (Set.Ioi 0) := by
        have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
            integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
          refine hc.norm.congr (Eventually.of_forall fun v => ?_)
          dsimp only
          rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine (h_exp.const_mul (2 / (Real.pi * Real.cos θ))).mono' (Continuous.aestronglyMeasurable ?_) ?_
        · refine Continuous.mul ?_ (Complex.continuous_exp.comp (by fun_prop))
          refine (Complex.continuous_ofReal.comp (by fun_prop)).div
            (continuous_const.mul (Complex.continuous_cos.comp (by fun_prop))) (fun v => ?_)
          exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (cos_ne_zero_of_abs_lt hθ)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hn : ‖Complex.exp (Complex.I * s * v)‖ = 1 := by
            rw [show Complex.I * (s : ℂ) * v = ((s * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, hn, mul_one]
          dsimp only [uTheta]
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤
              ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
            have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤
                ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
              have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
                rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
              have h1' : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
                have := Real.cosh_sq (Real.pi * v)
                have := Real.cos_sq_add_sin_sq θ
                nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
              rw [cos_normSq_eq]
              nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
            exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
          calc Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖)
              ≤ Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by gcongr
            _ = (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
                rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
                field_simp [Real.pi_ne_zero, hcos_pos.ne']
      have h_int_tot := h1.sub (h2.const_mul (Complex.I * s))
      have hW_tend : Tendsto W atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_bnd : ∀ᶠ v : ℝ in atTop, ‖W v‖ ≤ (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
          dsimp only [W]
          have hn : ‖Complex.exp (Complex.I * s * v)‖ = 1 := by
            rw [show Complex.I * (s : ℂ) * v = ((s * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, hn, mul_one, norm_neg]
          dsimp only [uTheta]
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤
              ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
            have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤
                ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
              have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
                rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
              have h1' : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
                have := Real.cosh_sq (Real.pi * v)
                have := Real.cos_sq_add_sin_sq θ
                nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
              rw [cos_normSq_eq]
              nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
            exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
          calc Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖)
              ≤ Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by gcongr
            _ = (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
                rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
                field_simp [Real.pi_ne_zero, hcos_pos.ne']
        have h_lim : Tendsto (fun v : ℝ => (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
          have h1' : Tendsto (fun v : ℝ => Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) :=
            Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(2 * Real.pi) < 0))
          simpa using h1'.const_mul (2 / (Real.pi * Real.cos θ))
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
          (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hW_deriv h_int_tot hW_tend
      rw [MeasureTheory.integral_sub h1 (h2.const_mul _), MeasureTheory.integral_const_mul] at hftc
      have hW0 : W 0 = -uTheta θ 0 := by simp [W]
      rw [hW0] at hftc
      linear_combination hftc
    have h_Psi_re : Ψ s = s * (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)).re := by
      dsimp only [Ψ]
      rw [h_ibp, Complex.add_im]
      have hu0 : (uTheta θ 0).im = 0 := by
        dsimp only [uTheta]
        simp only [Complex.ofReal_zero, mul_zero, neg_zero, add_zero, Real.exp_zero, Complex.ofReal_one,
          ← Complex.ofReal_cos, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]
      rw [hu0, zero_add]
      simp [Complex.mul_im]
    let p : ℝ := s / (2 * Real.pi)
    have h_cauchy_eq : ∀ ω : ℝ,
        ((1 / (1 / 4 + (p - ω) ^ 2) : ℝ) : ℂ) =
          ∫ x : ℝ, (Real.exp (-|x| / 2) : ℂ) * Complex.exp (Complex.I * (p - ω) * x) := by
      intro ω
      have h_half : ∀ a : ℝ, (∫ x in Set.Ioi (0 : ℝ),
          (Real.exp (-x / 2) : ℂ) * Complex.exp (Complex.I * a * x)) =
          1 / (1 / 2 - Complex.I * a) := by
        intro a
        have h_eq : (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * Complex.exp (Complex.I * a * x)) =
            fun x : ℝ => Complex.exp (-(1 / 2 - Complex.I * a) * x) := by
          ext x; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
        rw [h_eq]
        refine (integral_exp_mul_complex_Ioi (by simp) 0).trans ?_
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        rw [div_eq_mul_inv, show (-(1 / 2 - Complex.I * a)) = -(1 / 2 - Complex.I * a) by rfl, inv_neg]; ring
      let F : ℝ → ℂ := fun x => (Real.exp (-|x| / 2) : ℂ) * Complex.exp (Complex.I * (p - ω) * x)
      have hF_Ioi : IntegrableOn F (Set.Ioi 0) := by
        have h_eq : Set.EqOn F (fun x : ℝ => Complex.exp (-(1 / 2 - Complex.I * (p - ω)) * x)) (Set.Ioi 0) := by
          intro x hx; dsimp only [F]; rw [abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
        exact (integrableOn_exp_mul_complex_Ioi (by simp) 0).congr_fun (fun x hx => (h_eq hx).symm) measurableSet_Ioi
      have hF_Iio : IntegrableOn F (Set.Iio 0) := by
        have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
        have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext x; simp
        have h1 := (Measure.measurePreserving_neg volume).integrableOn_comp_preimage h_emb (s := Set.Iio 0)
        rw [h_pre] at h1
        apply h1.mp
        have h_eq : Set.EqOn (fun x => F (-x)) (fun x : ℝ => Complex.exp (-(1 / 2 + Complex.I * (p - ω)) * x)) (Set.Ioi 0) := by
          intro x hx; dsimp only [F]; rw [abs_neg, abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
        exact (integrableOn_exp_mul_complex_Ioi (by simp) 0).congr_fun (fun x hx => (h_eq hx).symm) measurableSet_Ioi
      have hF_Iic : IntegrableOn F (Set.Iic 0) := hF_Iio.congr_set_ae Iio_ae_eq_Iic.symm
      have h_split : (∫ x : ℝ, F x) = (∫ x in Set.Ioi (0 : ℝ), F x) + (∫ x in Set.Ioi (0 : ℝ), F (-x)) := by
        have h_univ : (∫ x : ℝ, F x) = (∫ x in Set.Iic (0 : ℝ), F x) + (∫ x in Set.Ioi (0 : ℝ), F x) := by
          rw [← MeasureTheory.setIntegral_univ, ← Set.Iic_union_Ioi,
            MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hF_Iic hF_Ioi]
        have h_Iio_Ioi : (∫ x in Set.Iio (0 : ℝ), F x) = ∫ x in Set.Ioi (0 : ℝ), F (-x) := by
          have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
          have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext x; simp
          have h_eq := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb F (Set.Iio 0)
          change ∫ x in (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0, F (-x) = ∫ y in Set.Iio 0, F y at h_eq
          rw [h_pre] at h_eq; exact h_eq.symm
        rw [h_univ, MeasureTheory.integral_Iic_eq_integral_Iio, h_Iio_Ioi, add_comm]
      have h1 : (∫ x in Set.Ioi (0 : ℝ), F x) = 1 / (1 / 2 - Complex.I * (p - ω)) := by
        have h_eq : Set.EqOn F (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * Complex.exp (Complex.I * (p - ω) * x)) (Set.Ioi 0) := by
          intro x hx; dsimp only [F]; rw [abs_of_pos hx]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
        simpa [Complex.ofReal_sub] using h_half (p - ω)
      have h2 : (∫ x in Set.Ioi (0 : ℝ), F (-x)) = 1 / (1 / 2 + Complex.I * (p - ω)) := by
        have h_eq : Set.EqOn (fun x => F (-x)) (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * Complex.exp (Complex.I * (-(p - ω)) * x)) (Set.Ioi 0) := by
          intro x hx; dsimp only [F]; rw [abs_neg, abs_of_pos hx]; push_cast; ring_nf
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
        have h_val := h_half (-(p - ω))
        rw [show ((-(p - ω) : ℝ) : ℂ) = -((p : ℂ) - ω) by push_cast; ring] at h_val
        rw [h_val]; ring
      rw [h_split, h1, h2]
      have hne1 : (1 / 2 : ℂ) - Complex.I * (p - ω) ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre
      have hne2 : (1 / 2 : ℂ) + Complex.I * (p - ω) ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre
      have h_alg : 1 / (1 / 4 + ((p : ℂ) - ω) ^ 2) = 1 / (1 / 2 - Complex.I * (p - ω)) + 1 / (1 / 2 + Complex.I * (p - ω)) := by
        rw [div_add_div _ _ hne1 hne2]
        have h1 : (1 : ℂ) * (1 / 2 + Complex.I * (p - ω)) + (1 / 2 - Complex.I * (p - ω)) * 1 = 1 := by ring
        have h2 : (1 / 2 - Complex.I * (p - ω)) * (1 / 2 + Complex.I * (p - ω)) = 1 / 4 + ((p : ℂ) - ω) ^ 2 := by
          linear_combination -((p : ℂ) - ω) ^ 2 * Complex.I_sq
        rw [h1, h2]
      push_cast; exact h_alg
    have h_fub_2d : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-2 * θ * q.1) / Real.cosh (Real.pi * q.1) : ℝ) : ℂ) *
        ((Real.exp (-|q.2| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - q.1) * q.2)) := by
      have h_w : Integrable (fun ω : ℝ => Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) := by
        have h_p : IntegrableOn (fun ω : ℝ => Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun ω : ℝ => Real.exp (-(Real.pi - 2 * |θ|) * ω)) (Set.Ioi 0) := by
            have h1 : IntegrableOn (fun ω : ℝ => Complex.exp ((-(Real.pi - 2 * |θ|) : ℂ) * ω)) (Set.Ioi 0) :=
              integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
            refine h1.norm.congr (Eventually.of_forall fun ω => ?_)
            dsimp only
            rw [show ((-(Real.pi - 2 * |θ|) : ℂ) * ω) = ((-(Real.pi - 2 * |θ|) * ω : ℝ) : ℂ) by push_cast; ring,
              ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine (hc.const_mul 2).mono' (Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop) (fun ω => (Real.cosh_pos _).ne'))) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
          rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]
          have hch : Real.exp (Real.pi * ω) / 2 ≤ Real.cosh (Real.pi * ω) := by
            rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * ω))]
          have h1 : Real.exp (-2 * θ * ω) ≤ Real.exp (2 * |θ| * ω) := by
            exact Real.exp_le_exp.mpr (by rw [show -2 * θ * ω = 2 * (-θ) * ω by ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (neg_le_abs θ) zero_le_two) hω.le)
          calc Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)
              ≤ Real.exp (2 * |θ| * ω) / (Real.exp (Real.pi * ω) / 2) := by gcongr
            _ = 2 * Real.exp (-(Real.pi - 2 * |θ|) * ω) := by
                rw [show -(Real.pi - 2 * |θ|) * ω = 2 * |θ| * ω - Real.pi * ω by ring, Real.exp_sub]; ring
        have h_n : IntegrableOn (fun ω : ℝ => Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) (Set.Iic 0) := by
          refine IntegrableOn.congr_set_ae ?_ Iio_ae_eq_Iic.symm
          have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
          have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext ω; simp
          have h1 := (Measure.measurePreserving_neg volume).integrableOn_comp_preimage h_emb (s := Set.Iio 0)
          rw [h_pre] at h1
          apply h1.mp
          have hc : IntegrableOn (fun ω : ℝ => Real.exp (-(Real.pi - 2 * |θ|) * ω)) (Set.Ioi 0) := by
            have h2 : IntegrableOn (fun ω : ℝ => Complex.exp ((-(Real.pi - 2 * |θ|) : ℂ) * ω)) (Set.Ioi 0) :=
              integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
            refine h2.norm.congr (Eventually.of_forall fun ω => ?_)
            dsimp only
            rw [show ((-(Real.pi - 2 * |θ|) : ℂ) * ω) = ((-(Real.pi - 2 * |θ|) * ω : ℝ) : ℂ) by push_cast; ring,
              ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine (hc.const_mul 2).mono' (Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop) (fun ω => (Real.cosh_pos _).ne'))) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
          rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _)), mul_neg, Real.cosh_neg]
          have hch : Real.exp (Real.pi * ω) / 2 ≤ Real.cosh (Real.pi * ω) := by
            rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * ω))]
          have h2 : Real.exp (-2 * θ * (-ω)) ≤ Real.exp (2 * |θ| * ω) := by
            exact Real.exp_le_exp.mpr (by rw [show -2 * θ * (-ω) = 2 * θ * ω by ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self θ) zero_le_two) hω.le)
          calc Real.exp (-2 * θ * (-ω)) / Real.cosh (Real.pi * ω)
              ≤ Real.exp (2 * |θ| * ω) / (Real.exp (Real.pi * ω) / 2) := by gcongr; exact div_pos (Real.exp_pos _) two_pos
            _ = 2 * Real.exp (-(Real.pi - 2 * |θ|) * ω) := by
                rw [show -(Real.pi - 2 * |θ|) * ω = 2 * |θ| * ω - Real.pi * ω by ring, Real.exp_sub]; ring
        rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi]
        exact h_n.union h_p
      have h_x : Integrable (fun x : ℝ => Real.exp (-|x| / 2)) := by
        have h_p : IntegrableOn (fun x : ℝ => Real.exp (-|x| / 2)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun x : ℝ => Complex.exp ((-1 / 2 : ℂ) * x)) (Set.Ioi 0) :=
            integrableOn_exp_mul_complex_Ioi (by simp; norm_num) 0
          refine hc.norm.congr ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
          rw [abs_of_pos hx, show ((-1 / 2 : ℂ) * x) = ((-x / 2 : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h_n : IntegrableOn (fun x : ℝ => Real.exp (-|x| / 2)) (Set.Iic 0) := by
          refine IntegrableOn.congr_set_ae ?_ Iio_ae_eq_Iic.symm
          have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
          have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext x; simp
          have h1 := (Measure.measurePreserving_neg volume).integrableOn_comp_preimage h_emb (s := Set.Iio 0)
          rw [h_pre] at h1
          apply h1.mp
          simpa [abs_neg] using h_p
        rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi]
        exact h_n.union h_p
      have h_prod_r := h_w.mul_prod h_x
      refine h_prod_r.mono' (Continuous.aestronglyMeasurable (Continuous.mul (Continuous.mul (Complex.continuous_ofReal.comp (Continuous.div (by fun_prop) (by fun_prop) (fun q => (Real.cosh_pos _).ne'))) (by fun_prop)) (by fun_prop))) ?_
      filter_upwards with q
      have hn : ‖Complex.exp (Complex.I * (p - q.1) * q.2)‖ = 1 := by
        rw [show Complex.I * ((p : ℂ) - (q.1 : ℂ)) * q.2 = (((p - q.1) * q.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hn, mul_one, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _)),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h_swap := MeasureTheory.integral_integral_swap (f := fun ω x => ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) * ((Real.exp (-|x| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * x)) h_fub_2d
    let H : ℝ → ℂ := fun x => (Real.exp (-|x| / 2) : ℂ) * Complex.exp (Complex.I * p * x) /
      Complex.cos (θ + Complex.I * x / 2)
    have hH_ae : ∀ᵐ x : ℝ ∂volume,
        (∫ ω : ℝ, ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) *
          ((Real.exp (-|x| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * x)) = H x := by
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      have h_eq : (fun ω : ℝ => ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) *
          ((Real.exp (-|x| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * x)) =
          fun ω : ℝ => ((Real.exp (-|x| / 2) : ℂ) * Complex.exp (Complex.I * p * x)) *
            ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) * Complex.exp (-Complex.I * ω * x)) := by
        ext ω
        rw [show Complex.I * ((p : ℂ) - (ω : ℂ)) * x = Complex.I * p * x + (-Complex.I * ω * x) by push_cast; ring,
          Complex.exp_add]
        push_cast; ring
      rw [h_eq, MeasureTheory.integral_const_mul, cosh_fourier_eq hθ hx]
      dsimp only [H]; ring
    have hH_int : Integrable H := h_fub_2d.integral_prod_right.congr hH_ae
    have h_lhs_eq : ((∫ ω : ℝ, (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) : ℝ) : ℂ) =
        ∫ x : ℝ, H x := by
      trans (∫ ω : ℝ, (((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) : ℝ) : ℂ))
      · exact integral_ofReal.symm
      have h1 : (∫ ω : ℝ, ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) : ℝ) : ℂ) =
          ∫ ω : ℝ, ∫ x : ℝ, ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) *
            ((Real.exp (-|x| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * x) := by
        congr 1; ext ω
        rw [show ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) : ℝ) =
            (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) * (1 / (1 / 4 + (p - ω) ^ 2)) by ring,
          Complex.ofReal_mul, h_cauchy_eq ω, ← MeasureTheory.integral_const_mul]
        congr 1; ext x; ring
      rw [h1, h_swap]
      exact MeasureTheory.integral_congr_ae hH_ae
    have hH_split : (∫ x : ℝ, H x) = (∫ x in Set.Ioi (0 : ℝ), H x) + (∫ x in Set.Ioi (0 : ℝ), H (-x)) := by
      have h_univ : (∫ x : ℝ, H x) = (∫ x in Set.Iic (0 : ℝ), H x) + (∫ x in Set.Ioi (0 : ℝ), H x) := by
        rw [← MeasureTheory.setIntegral_univ, ← Set.Iic_union_Ioi,
          MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
            hH_int.integrableOn hH_int.integrableOn]
      have h_Iio_Ioi : (∫ x in Set.Iio (0 : ℝ), H x) = ∫ x in Set.Ioi (0 : ℝ), H (-x) := by
        have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
        have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext x; simp
        have h_eq := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb H (Set.Iio 0)
        change ∫ x in (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0, H (-x) = ∫ y in Set.Iio 0, H y at h_eq
        rw [h_pre] at h_eq; exact h_eq.symm
      rw [h_univ, MeasureTheory.integral_Iic_eq_integral_Iio, h_Iio_Ioi, add_comm]
    have hH_conj : ∀ x : ℝ, H (-x) = starRingEnd ℂ (H x) := by
      intro x; dsimp only [H]
      rw [map_div₀, map_mul, Complex.conj_ofReal, abs_neg, ← Complex.exp_conj, ← Complex.cos_conj]
      congr 2
      · simp [map_mul, Complex.conj_I, map_ofNat]
      · simp [map_add, map_div₀, map_mul, Complex.conj_I, map_ofNat]
    have h_scale : (∫ x in Set.Ioi (0 : ℝ), H x) =
        2 * Real.pi ^ 2 * (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)) := by
      have h_sub : (∫ x in Set.Ioi (0 : ℝ), H x) =
          (2 * Real.pi) • ∫ v in Set.Ioi (0 : ℝ), H (2 * Real.pi * v) := by
        have h := MeasureTheory.integral_comp_mul_left_Ioi H (0 : ℝ) (by positivity : 0 < 2 * Real.pi)
        rw [mul_zero] at h
        rw [h, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      rw [h_sub, Complex.real_smul, ← MeasureTheory.integral_const_mul]
      rw [show (2 : ℂ) * (Real.pi : ℂ) ^ 2 * ∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v) =
          ∫ v in Set.Ioi (0 : ℝ), ((2 * Real.pi ^ 2 : ℝ) : ℂ) * (uTheta θ v * Complex.exp (Complex.I * s * v)) by
        rw [MeasureTheory.integral_const_mul]; push_cast; ring]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      dsimp only [H, uTheta, p]
      rw [abs_of_pos (mul_pos (by positivity) hv)]
      have h1 : -(2 * Real.pi * v) / 2 = -Real.pi * v := by ring
      have h2 : Complex.I * ((s / (2 * Real.pi) : ℝ) : ℂ) * ((2 * Real.pi * v : ℝ) : ℂ) =
          Complex.I * s * v := by push_cast; field_simp [Real.pi_ne_zero]
      have h3 : Complex.I * ((2 * Real.pi * v : ℝ) : ℂ) / 2 = Complex.I * Real.pi * v := by
        push_cast; ring
      rw [h1, h2, h3]
      push_cast; field_simp [Real.pi_ne_zero]
    have h_re_id : (∫ ω : ℝ, (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2)) =
        4 * Real.pi ^ 2 * (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)).re := by
      have h_c : ((∫ ω : ℝ, (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) : ℝ) : ℂ) =
          (∫ x in Set.Ioi (0 : ℝ), H x) + starRingEnd ℂ (∫ x in Set.Ioi (0 : ℝ), H x) := by
        rw [h_lhs_eq, hH_split]
        congr 1
        simp_rw [hH_conj]
        have h_cc := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm (hH_int.integrableOn (s := Set.Ioi 0))
        simpa [Complex.conjCLE_apply] using h_cc
      have h_re := congr_arg Complex.re h_c
      simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at h_re
      rw [h_re, h_scale]
      have h_eq : (2 * (Real.pi : ℂ) ^ 2 * ∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)).re =
          2 * Real.pi ^ 2 * (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)).re := by
        rw [show 2 * (Real.pi : ℂ) ^ 2 = ((2 * Real.pi ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
      linarith
    have h_int_pos : 0 < ∫ ω : ℝ, (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2) := by
      let q_fn : ℝ → ℝ := fun ω => (Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω)) / (1 / 4 + (p - ω) ^ 2)
      have hq_int : Integrable q_fn := by
        have h_c_int : Integrable (fun ω : ℝ =>
            ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) / ((1 / 4 + (p - ω) ^ 2 : ℝ) : ℂ)) := by
          have h_bd := h_fub_2d.integral_prod_left
          refine h_bd.congr (Eventually.of_forall fun ω => ?_)
          dsimp only
          have h_eq : (fun y : ℝ => ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) *
              ((Real.exp (-|y| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * y)) =
              fun y : ℝ => ((Real.exp (-2 * θ * ω) / Real.cosh (Real.pi * ω) : ℝ) : ℂ) *
                (((Real.exp (-|y| / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (p - ω) * y)) := by ext y; ring
          rw [h_eq, MeasureTheory.integral_const_mul, ← h_cauchy_eq ω]
          push_cast; ring
        have h_r := Complex.reCLM.integrable_comp h_c_int
        refine h_r.congr (Eventually.of_forall fun ω => ?_)
        dsimp only [Complex.reCLM_apply, q_fn]
        rw [← Complex.ofReal_div, Complex.ofReal_re]
      have hq_cont : Continuous q_fn :=
        ((Real.continuous_exp.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
          (fun ω => (Real.cosh_pos _).ne')).div (by fun_prop) (fun ω => by positivity)
      obtain ⟨ω_min, _, hω_isMin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn ⟨(0 : ℝ), by norm_num⟩ hq_cont.continuousOn
      have h_min_pos : 0 < q_fn ω_min := by
        dsimp only [q_fn]; exact div_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _)) (by positivity)
      have h_Ioc_le : ∫ ω in Set.Ioc (0 : ℝ) 1, q_fn ω ≤ ∫ ω : ℝ, q_fn ω := by
        refine MeasureTheory.setIntegral_le_integral hq_int ?_
        filter_upwards with ω
        dsimp only [q_fn]; exact div_nonneg (div_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le) (by positivity)
      have h_min_le : q_fn ω_min ≤ ∫ ω in Set.Ioc (0 : ℝ) 1, q_fn ω := by
        have h_c : ∫ _ in Set.Ioc (0 : ℝ) 1, q_fn ω_min = q_fn ω_min := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]; norm_num
        rw [← h_c]
        have h_c_int : IntegrableOn (fun _ : ℝ => q_fn ω_min) (Set.Ioc 0 1) :=
          (continuousOn_const : ContinuousOn (fun _ : ℝ => q_fn ω_min) (Set.Icc 0 1)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        have h_q_int : IntegrableOn q_fn (Set.Ioc 0 1) :=
          (hq_cont.continuousOn : ContinuousOn q_fn (Set.Icc 0 1)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        refine MeasureTheory.setIntegral_mono_on h_c_int h_q_int measurableSet_Ioc fun ω hω => hω_isMin (Set.Ioc_subset_Icc_self hω)
      linarith
    rw [h_Psi_re]
    have : 0 < (∫ v in Set.Ioi (0 : ℝ), uTheta θ v * Complex.exp (Complex.I * s * v)).re := by nlinarith [Real.pi_pos]
    exact mul_pos hs this
  rw [h_J_laplace]
  have h_cont_Psi : Continuous Ψ := by
    have h_unif : Continuous (fun s : ℝ => ∫ v in Set.Ioi (0 : ℝ), cTheta θ v * Complex.exp (Complex.I * s * v)) := by
      refine MeasureTheory.continuous_of_dominated
        (bound := fun v => (4 / Real.cos θ ^ 2) * Real.exp (-2 * Real.pi * v)) ?_ ?_ ?_ ?_
      · intro s
        refine Continuous.aestronglyMeasurable ?_
        refine Continuous.mul ?_ (Complex.continuous_exp.comp (by fun_prop))
        refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
        exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
      · intro s
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        have hn : ‖Complex.exp (Complex.I * s * v)‖ = 1 := by
          rw [show Complex.I * (s : ℂ) * v = ((s * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, hn, mul_one]
        exact cTheta_norm_le hθ hv.le
      · have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
          have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
            integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
          refine hc.norm.congr (Eventually.of_forall fun v => ?_)
          dsimp only
          rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact h_exp.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        exact Continuous.mul continuous_const (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
    exact Complex.continuous_im.comp h_unif
  have h_lap_int : IntegrableOn (fun s : ℝ => Real.exp (-s * y) * Ψ s) (Set.Ioi 0) := by
    have h_bd : ∀ s : ℝ, |Ψ s| ≤ ∫ v in Set.Ioi (0 : ℝ), ‖cTheta θ v‖ := by
      intro s
      dsimp only [Ψ]
      refine (Complex.abs_im_le_norm _).trans ?_
      refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
      congr 1; ext v
      have hn : ‖Complex.exp (Complex.I * s * v)‖ = 1 := by
        rw [show Complex.I * (s : ℂ) * v = ((s * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hn, mul_one]
    have h_e2 : IntegrableOn (fun s : ℝ => Real.exp (-s * y)) (Set.Ioi 0) := by
      have hc : IntegrableOn (fun s : ℝ => Complex.exp ((-y : ℂ) * s)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp [hy]) 0
      refine hc.norm.congr (Eventually.of_forall fun s => ?_)
      dsimp only
      rw [show ((-y : ℂ) * s) = ((-s * y : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (h_e2.const_mul (∫ v in Set.Ioi (0 : ℝ), ‖cTheta θ v‖)).mono'
      (Continuous.aestronglyMeasurable ((Real.continuous_exp.comp (by fun_prop)).mul h_cont_Psi)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (h_bd s) (Real.exp_pos _).le
  have h_prod_cont : Continuous (fun s : ℝ => Real.exp (-s * y) * Ψ s) :=
    (Real.continuous_exp.comp (by fun_prop)).mul h_cont_Psi
  obtain ⟨s_min, hs_min, hs_isMin⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMinOn ⟨(1 : ℝ), by norm_num⟩ h_prod_cont.continuousOn
  have hs_pos : 0 < Real.exp (-s_min * y) * Ψ s_min :=
    mul_pos (Real.exp_pos _) (h_Psi_pos s_min (by linarith [hs_min.1]))
  have h_Ioc_le : ∫ s in Set.Ioc (1 : ℝ) 2, Real.exp (-s * y) * Ψ s ≤
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * y) * Ψ s := by
    refine MeasureTheory.setIntegral_mono_set h_lap_int ?_
      (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi zero_le_one)).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (h_Psi_pos s hs).le
  have h_min_le : Real.exp (-s_min * y) * Ψ s_min ≤
      ∫ s in Set.Ioc (1 : ℝ) 2, Real.exp (-s * y) * Ψ s := by
    have h_c : ∫ _ in Set.Ioc (1 : ℝ) 2, Real.exp (-s_min * y) * Ψ s_min = Real.exp (-s_min * y) * Ψ s_min := by
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]; norm_num
    rw [← h_c]
    have h_c_int : IntegrableOn (fun _ : ℝ => Real.exp (-s_min * y) * Ψ s_min) (Set.Ioc 1 2) :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => Real.exp (-s_min * y) * Ψ s_min) (Set.Icc 1 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have h_p_int : IntegrableOn (fun s : ℝ => Real.exp (-s * y) * Ψ s) (Set.Ioc 1 2) :=
      (h_prod_cont.continuousOn : ContinuousOn (fun s : ℝ => Real.exp (-s * y) * Ψ s) (Set.Icc 1 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    refine MeasureTheory.setIntegral_mono_on h_c_int h_p_int measurableSet_Ioc fun s hs => hs_isMin (Set.Ioc_subset_Icc_self hs)
  linarith

/-- **Lemma 3.3 (Part 1)**: Positivity `J(y, θ) > 0` for all `y ≠ 0`. -/
theorem limitingJ_pos (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∀ y : ℝ, y ≠ 0 → limitingJ y θ > 0 := by
  intro y hy
  rcases lt_or_gt_of_ne hy with hy_neg | hy_pos
  · by_cases hθ_nonneg : 0 ≤ θ
    · exact limitingJ_pos_of_neg hθ_nonneg (abs_lt.mp hθ).2 hy_neg
    · rw [← limitingJ_neg_neg]
      exact limitingJ_pos_of_pos (by rwa [abs_neg]) (by linarith)
  · exact limitingJ_pos_of_pos hθ hy_pos

end PolarEvaluation
