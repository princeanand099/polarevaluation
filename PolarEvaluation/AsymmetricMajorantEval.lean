import PolarEvaluation.AsymmetricMajorantDiffB

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

lemma integral_inv_add_sq_R {c R : ℝ} (hR : 0 < R) :
    ∫ x : ℝ, 1 / ((x - c) ^ 2 + R ^ 2) = Real.pi / R := by
  have h1 : ∫ x : ℝ, 1 / ((x - c) ^ 2 + R ^ 2) = ∫ x : ℝ, 1 / (x ^ 2 + R ^ 2) :=
    integral_sub_right_eq_self (fun x => 1 / (x ^ 2 + R ^ 2)) volume c
  rw [h1]
  have h2 : (fun x : ℝ => 1 / (x ^ 2 + R ^ 2)) = fun x : ℝ => (1 / R ^ 2) * (1 + ((1 / R) * x) ^ 2)⁻¹ := by
    ext x; field_simp [hR.ne']; ring
  rw [h2, integral_const_mul, integral_univ_inv_one_add_mul_sq (1 / R),
    abs_of_pos (by positivity : 0 < 1 / R)]
  field_simp [hR.ne']

lemma vaaler_integral_eq_tsum (θ Δ α : ℝ) (hθ : |θ| < Real.pi / 2)
    (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hsumm_b : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)))
    (hsum0 : ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0)
    (h_int_M : Integrable (fun x : ℝ => majorantM θ Δ α x))
    (h_sup_M : ∃ C > 0, ∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x| ≤ C) :
    (∫ y : ℝ, vaalerInterpolant θ Δ α y) = ∑' n : ℤ, rescaledF θ Δ (n + α) := by
  have hΔ_pos : 0 < Δ := by linarith
  have ha_summ : Summable (fun n : ℤ => |rescaledF θ Δ (n + α)|) := rescaledF_summable θ Δ α hΔ hα
  have hb_summ : Summable (fun n : ℤ => |rescaledFDeriv θ Δ (n + α)|) := hsumm_b.abs
  have hbm_summ : Summable (fun n : ℤ => |(n + α) * rescaledFDeriv θ Δ (n + α)|) :=
    rescaledFDeriv_mul_summable θ Δ α hΔ hα
  let S_a : ℝ := ∑' n : ℤ, |rescaledF θ Δ (n + α)|
  let S_b : ℝ := ∑' n : ℤ, |rescaledFDeriv θ Δ (n + α)|
  let S_bm : ℝ := ∑' n : ℤ, |(n + α) * rescaledFDeriv θ Δ (n + α)|
  obtain ⟨⟨hM_diff, _⟩, hM_re⟩ := majorantEntire_props θ Δ α hΔ hα hsumm_b
  let M_α : ℂ → ℂ := fun z => majorantEntire θ Δ α (z / Δ)
  have hMα_diff : Differentiable ℂ M_α :=
    hM_diff.comp (differentiable_id.div_const (Δ : ℂ))
  have hMα_real : ∀ y : ℝ, M_α y = (vaalerInterpolant θ Δ α y : ℂ) := by
    intro y
    dsimp only [M_α]
    rw [show (y : ℂ) / (Δ : ℂ) = ((y / Δ : ℝ) : ℂ) by push_cast; ring]
    have h1 := hM_re (y / Δ)
    apply Complex.ext
    · rw [h1.2]; unfold majorantM; congr 1; field_simp [hΔ_pos.ne']
    · exact h1.1
  let f : ℝ → ℂ := fun y => (vaalerInterpolant θ Δ α y : ℂ)
  have hf_cont : Continuous f := by
    have heq : f = fun y : ℝ => M_α y := by ext y; exact (hMα_real y).symm
    rw [heq]; exact hMα_diff.continuous.comp Complex.continuous_ofReal
  obtain ⟨C_s, hC_s, h_sup⟩ := h_sup_M
  have hf_decay : ∃ C, ∀ y : ℝ, ‖f y‖ ≤ C * (1 + |y|) ^ (-2 : ℝ) := by
    refine ⟨2 * Δ ^ 2 * C_s, fun y => ?_⟩
    have h1 := h_sup (y / Δ)
    have h_m : majorantM θ Δ α (y / Δ) = vaalerInterpolant θ Δ α y := by
      unfold majorantM; congr 1; field_simp [hΔ_pos.ne']
    rw [h_m] at h1
    have h_1y : (1 + y ^ 2) * |vaalerInterpolant θ Δ α y| ≤ Δ ^ 2 * C_s := by
      have h_le : 1 + y ^ 2 ≤ Δ ^ 2 * (1 + (y / Δ) ^ 2) := by
        have : Δ ^ 2 * (1 + (y / Δ) ^ 2) = Δ ^ 2 + y ^ 2 := by field_simp [hΔ_pos.ne']
        nlinarith [sq_nonneg Δ]
      calc (1 + y ^ 2) * |vaalerInterpolant θ Δ α y|
          ≤ Δ ^ 2 * (1 + (y / Δ) ^ 2) * |vaalerInterpolant θ Δ α y| := by gcongr
        _ = Δ ^ 2 * ((1 + (y / Δ) ^ 2) * |vaalerInterpolant θ Δ α y|) := by ring
        _ ≤ Δ ^ 2 * C_s := by gcongr
    have h_pos : 0 < 1 + |y| := by positivity
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg h_pos.le, Real.rpow_natCast]
    have h_1y2 : (1 + |y|) ^ 2 ≤ 2 * (1 + y ^ 2) := by
      have : (1 - |y|) ^ 2 ≥ 0 := sq_nonneg _; nlinarith [sq_abs y]
    dsimp only [f]
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |vaalerInterpolant θ Δ α y| ≤ (Δ ^ 2 * C_s) / (1 + y ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = (2 * Δ ^ 2 * C_s) / (2 * (1 + y ^ 2)) := by ring
      _ ≤ (2 * Δ ^ 2 * C_s) / (1 + |y|) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) h_1y2
      _ = (2 * Δ ^ 2 * C_s) * ((1 + |y|) ^ 2)⁻¹ := div_eq_mul_inv _ _
  have hf_int : Integrable f := by
    have h_eq : f = fun y : ℝ => ((majorantM θ Δ α (y / Δ) : ℝ) : ℂ) := by
      ext y; dsimp only [f, majorantM]; congr 2; field_simp [hΔ_pos.ne']
    rw [h_eq]
    exact (h_int_M.comp_div hΔ_pos.ne').ofReal
  have hf_fourier_zero : ∀ ξ : ℝ, 1 ≤ |ξ| → 𝓕 f ξ = 0 := by
    intro ξ hξ
    have h_sin_bd : ∀ w : ℂ, ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
      intro w
      have hsin_def : Complex.sin w = (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by unfold Complex.sin; ring_nf
      rw [hsin_def]
      have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact le_abs_self _)
      have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact neg_le_abs _)
      calc ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
          = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
            rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
        _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by gcongr; exact norm_sub_le _ _
        _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by gcongr
        _ = Real.exp |w.im| := by ring
    let s : ℝ := if 0 < ξ then -1 else 1
    have hξs : ξ * s = -|ξ| := by
      dsimp only [s]; split_ifs with h
      · rw [abs_of_pos h]; ring
      · rw [abs_of_nonpos (not_lt.mp h)]; ring
    have hs_abs : |s| = 1 := by dsimp only [s]; split_ifs <;> norm_num
    have hMα_eq : ∀ z : ℂ, M_α z = ∑' n : ℤ, ((rescaledF θ Δ (n + α) : ℂ) * sincPi (z - n - α) ^ 2 +
        (rescaledFDeriv θ Δ (n + α) : ℂ) * (z - n - α) * sincPi (z - n - α) ^ 2) := by
      intro z; dsimp only [M_α, majorantEntire]
      congr 1; ext n
      have h_mul : (Δ : ℂ) * (z / Δ) = z := mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr hΔ_pos.ne')
      rw [h_mul]
    have h_rect_bd : ∀ R : ℝ, 1 ≤ R → ‖𝓕 f ξ‖ ≤ (S_a + S_bm) / (Real.pi * R) := by
      intro R hR
      have hR_pos : 0 < R := by linarith
      let g : ℂ → ℂ := fun z => M_α z * Complex.exp (-2 * Real.pi * Complex.I * ξ * z)
      have hg_diff : Differentiable ℂ g :=
        hMα_diff.mul (Complex.differentiable_exp.comp (differentiable_id.const_mul _))
      let C_v : ℝ := 4 * (S_a + S_b) * Real.exp (2 * Real.pi * R + 4) + 192 * Δ ^ 2 * Real.exp (2 * Real.pi * R + 4)
      have h_vert_bd : ∀ L : ℝ, 2 * Δ ≤ L → ∀ (x : ℝ), |x| = L → ∀ y : ℝ, |y| ≤ R →
          ‖M_α (x + Complex.I * y)‖ ≤ C_v / L := by
        intro L hL x hx y hy
        have hL_pos : 0 < L := by linarith
        rw [hMα_eq]
        let term_z : ℤ → ℂ := fun n =>
          (rescaledF θ Δ (n + α) : ℂ) * sincPi ((x + Complex.I * y) - n - α) ^ 2 +
            (rescaledFDeriv θ Δ (n + α) : ℂ) * ((x + Complex.I * y) - n - α) * sincPi ((x + Complex.I * y) - n - α) ^ 2
        have h_s_tz : Summable term_z := by
          refine ((ha_summ.add hb_summ).mul_right (Real.exp (2 * Real.pi * R + 4))).of_norm_bounded fun n => ?_
          have hsb := sincPi_bound ((x + Complex.I * y) - n - α)
          have him : |((x + Complex.I * y) - n - α).im| ≤ R := by
            simpa [Complex.sub_im, Complex.add_im, Complex.mul_im] using hy
          have hs1 : ‖sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤ Real.exp (2 * Real.pi * R + 4) := by
            rw [norm_pow]
            calc ‖sincPi ((x + Complex.I * y) - n - α)‖ ^ 2 ≤ (Real.exp (Real.pi * R + 2)) ^ 2 := by
                  gcongr; exact hsb.1.trans (Real.exp_le_exp.mpr (by gcongr))
              _ = Real.exp (2 * Real.pi * R + 4) := by rw [← Real.exp_nat_mul]; ring_nf
          have hs2 : ‖((x + Complex.I * y) - n - α) * sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤
              Real.exp (2 * Real.pi * R + 4) := hsb.2.trans (Real.exp_le_exp.mpr (by gcongr))
          dsimp only [term_z]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc ((rescaledFDeriv θ Δ (n + α) : ℝ) : ℂ),
            norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |rescaledF θ Δ (n + α)| * _ + |rescaledFDeriv θ Δ (n + α)| * _
              ≤ |rescaledF θ Δ (n + α)| * Real.exp (2 * Real.pi * R + 4) +
                |rescaledFDeriv θ Δ (n + α)| * Real.exp (2 * Real.pi * R + 4) := by gcongr
            _ = _ := by ring
        let F_near : Finset ℤ := Finset.Icc (-Int.ceil (2 * L)) (Int.ceil (2 * L))
        let f_far : ℤ → ℝ := fun n => 4 * (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|) *
          Real.exp (2 * Real.pi * R + 4) / L
        let f_near : ℤ → ℝ := fun n => if n ∈ F_near then (32 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4) else 0
        have hf_far_s : Summable f_far :=
          ((ha_summ.add hb_summ).mul_left (4 * Real.exp (2 * Real.pi * R + 4) / L)).congr fun n => by dsimp only [f_far]; ring
        have hf_near_s : Summable f_near := summable_of_ne_finset_zero (s := F_near) (fun n hn => by simp [f_near, hn])
        have h_term_le : ∀ n : ℤ, ‖term_z n‖ ≤ f_far n + f_near n := by
          intro n
          have him : |((x + Complex.I * y) - n - α).im| ≤ R := by
            simpa [Complex.sub_im, Complex.add_im, Complex.mul_im] using hy
          by_cases h_far : L / 2 ≤ |x - n - α|
          · have h_u_lb : L / 2 ≤ ‖(x + Complex.I * y) - n - α‖ := by
              have hre : ((x + Complex.I * y) - n - α).re = x - n - α := by simp; ring
              rw [← hre]; exact h_far.trans (Complex.abs_re_le_norm _)
            have h_u_ne : (x + Complex.I * y) - n - α ≠ 0 := norm_ne_zero_iff.mp (by linarith)
            have hs_1 : ‖sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤ 4 * Real.exp (2 * Real.pi * R) / L ^ 2 := by
              dsimp only [sincPi]; simp only [if_neg h_u_ne]
              rw [div_pow, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
              have h_sin := h_sin_bd (Real.pi * ((x + Complex.I * y) - n - α))
              have h_pim : |(Real.pi * ((x + Complex.I * y) - n - α)).im| ≤ Real.pi * R := by
                simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]; exact mul_le_mul_of_nonneg_left hy Real.pi_pos.le
              have h_s2 : ‖Complex.sin (Real.pi * ((x + Complex.I * y) - n - α))‖ ^ 2 ≤ Real.exp (2 * Real.pi * R) := by
                calc ‖Complex.sin _‖ ^ 2 ≤ Real.exp (Real.pi * R) ^ 2 := by gcongr; exact h_sin.trans (Real.exp_le_exp.mpr h_pim)
                  _ = Real.exp (2 * Real.pi * R) := by rw [← Real.exp_nat_mul]; ring_nf
              have h_den : Real.pi ^ 2 * (L / 2) ^ 2 ≤ (Real.pi * ‖(x + Complex.I * y) - n - α‖) ^ 2 := by
                rw [mul_pow]; gcongr
              have h_pi1 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
              calc ‖Complex.sin _‖ ^ 2 / (Real.pi * ‖(x + Complex.I * y) - n - α‖) ^ 2
                  ≤ Real.exp (2 * Real.pi * R) / (1 * (L / 2) ^ 2) := by
                    refine div_le_div₀ (by positivity) h_s2 (by positivity) ?_
                    calc 1 * (L / 2) ^ 2 ≤ Real.pi ^ 2 * (L / 2) ^ 2 := by gcongr
                      _ ≤ _ := h_den
                _ = 4 * Real.exp (2 * Real.pi * R) / L ^ 2 := by ring
            have hs_2 : ‖((x + Complex.I * y) - n - α) * sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤
                2 * Real.exp (2 * Real.pi * R) / L := by
              dsimp only [sincPi]; simp only [if_neg h_u_ne]
              have h_eq : ((x + Complex.I * y) - n - α) * (Complex.sin (Real.pi * ((x + Complex.I * y) - n - α)) /
                  (Real.pi * ((x + Complex.I * y) - n - α))) ^ 2 =
                  Complex.sin (Real.pi * ((x + Complex.I * y) - n - α)) ^ 2 / ((Real.pi ^ 2 : ℂ) * ((x + Complex.I * y) - n - α)) := by
                have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
                field_simp [hpi, h_u_ne]; ring
              rw [h_eq, norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
              have h_sin := h_sin_bd (Real.pi * ((x + Complex.I * y) - n - α))
              have h_pim : |(Real.pi * ((x + Complex.I * y) - n - α)).im| ≤ Real.pi * R := by
                simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]; exact mul_le_mul_of_nonneg_left hy Real.pi_pos.le
              have h_s2 : ‖Complex.sin (Real.pi * ((x + Complex.I * y) - n - α))‖ ^ 2 ≤ Real.exp (2 * Real.pi * R) := by
                calc ‖Complex.sin _‖ ^ 2 ≤ Real.exp (Real.pi * R) ^ 2 := by gcongr; exact h_sin.trans (Real.exp_le_exp.mpr h_pim)
                  _ = Real.exp (2 * Real.pi * R) := by rw [← Real.exp_nat_mul]; ring_nf
              have h_pi1 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
              calc ‖Complex.sin _‖ ^ 2 / (Real.pi ^ 2 * ‖(x + Complex.I * y) - n - α‖)
                  ≤ Real.exp (2 * Real.pi * R) / (1 * (L / 2)) := by
                    refine div_le_div₀ (by positivity) h_s2 (by positivity) (mul_le_mul h_pi1 h_u_lb (by positivity) (by positivity))
                _ = 2 * Real.exp (2 * Real.pi * R) / L := by ring
            have hL1 : 1 ≤ L := by linarith
            have hs_1' : ‖sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤ 4 * Real.exp (2 * Real.pi * R + 4) / L := by
              calc _ ≤ 4 * Real.exp (2 * Real.pi * R) / L ^ 2 := hs_1
                _ ≤ 4 * Real.exp (2 * Real.pi * R + 4) / L :=
                    div_le_div₀ (by positivity) (by gcongr; linarith) hL_pos (by nlinarith)
            have hs_2' : ‖((x + Complex.I * y) - n - α) * sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤
                4 * Real.exp (2 * Real.pi * R + 4) / L := by
              calc _ ≤ 2 * Real.exp (2 * Real.pi * R) / L := hs_2
                _ ≤ 4 * Real.exp (2 * Real.pi * R + 4) / L := by gcongr; linarith
            dsimp only [term_z]
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc ((rescaledFDeriv θ Δ (n + α) : ℝ) : ℂ),
              norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hfn_nn : 0 ≤ f_near n := by dsimp only [f_near]; split_ifs <;> positivity
            calc |rescaledF θ Δ (n + α)| * _ + |rescaledFDeriv θ Δ (n + α)| * _
                ≤ |rescaledF θ Δ (n + α)| * (4 * Real.exp (2 * Real.pi * R + 4) / L) +
                  |rescaledFDeriv θ Δ (n + α)| * (4 * Real.exp (2 * Real.pi * R + 4) / L) := by gcongr
              _ = f_far n := by dsimp only [f_far]; ring
              _ ≤ f_far n + f_near n := by linarith
          · have h_near : |x - n - α| < L / 2 := not_le.mp h_far
            have h_mem : n ∈ F_near := by
              have hn_abs : |(n : ℝ)| ≤ 2 * L := by
                have h1 : |(n : ℝ)| ≤ |x| + |x - n - α| + |α| := by
                  have : (n : ℝ) = x - (x - n - α) - α := by ring
                  rw [this]
                  calc |x - (x - n - α) - α| ≤ |x - (x - n - α)| + |α| := abs_sub _ _
                    _ ≤ |x| + |x - n - α| + |α| := by gcongr; exact abs_sub _ _
                have hα1 : |α| ≤ 1 := by rw [abs_of_pos hα.1]; exact hα.2.le
                linarith
              simp only [F_near, Finset.mem_Icc]
              have h_ceil := Int.le_ceil (2 * L)
              constructor
              · have : -(2 * L) ≤ (n : ℝ) := by linarith [(abs_le.mp hn_abs).1]
                exact_mod_cast (by linarith : (-Int.ceil (2 * L) : ℝ) - 1 < n) |> fun h' => Int.le_of_lt_add_one (by omega)
              · have : (n : ℝ) ≤ 2 * L := (abs_le.mp hn_abs).2
                exact_mod_cast (by linarith : (n : ℝ) < Int.ceil (2 * L) + 1) |> fun h' => Int.le_of_lt_add_one (by omega)
            have h_na : L / 2 < |(n : ℝ) + α| := by
              have h1 := abs_sub_abs_le_abs_sub x (n + α)
              rw [hx] at h1
              linarith [show |x - ((n : ℝ) + α)| = |x - n - α| by ring_nf]
            have h_na_ge_Δ : 1 ≤ |((n : ℝ) + α) / Δ| := by
              rw [abs_div, abs_of_pos hΔ_pos, one_le_div hΔ_pos]; linarith
            have hF_n : |rescaledF θ Δ (n + α)| ≤ 16 * Δ ^ 2 / L ^ 2 := by
              unfold rescaledF
              have hbd := kernelK_bound_large θ h_na_ge_Δ
              have heq : 4 / (((n : ℝ) + α) / Δ) ^ 2 = 4 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := by
                have hne : (n : ℝ) + α ≠ 0 := by intro h0; rw [h0, abs_zero] at h_na; linarith
                field_simp [hne, hΔ_pos.ne']; ring
              rw [heq] at hbd
              have hsq : L ^ 2 / 4 ≤ ((n : ℝ) + α) ^ 2 := by rw [← sq_abs ((n : ℝ) + α)]; nlinarith
              calc |kernelK θ (((n : ℝ) + α) / Δ)| ≤ 4 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := hbd
                _ ≤ 4 * Δ ^ 2 / (L ^ 2 / 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
                _ = 16 * Δ ^ 2 / L ^ 2 := by ring
            have hFd_n : |rescaledFDeriv θ Δ (n + α)| ≤ 16 * Δ ^ 2 / L ^ 2 := by
              have hne : (n : ℝ) + α ≠ 0 := by intro h0; rw [h0, abs_zero] at h_na; linarith
              have hbm := rescaledFDeriv_mul_bound θ Δ (n + α) hΔ_pos hne
              rw [abs_mul] at hbm
              have h_na1 : 1 ≤ |(n : ℝ) + α| := by linarith
              have hb1 : |rescaledFDeriv θ Δ (n + α)| ≤ 2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := by
                calc |rescaledFDeriv θ Δ (n + α)| ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| := by
                      rw [abs_mul]; exact le_mul_of_one_le_left (abs_nonneg _) h_na1
                  _ ≤ 2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := hbm
              have hsq : L ^ 2 / 4 ≤ ((n : ℝ) + α) ^ 2 := by rw [← sq_abs ((n : ℝ) + α)]; nlinarith
              calc |rescaledFDeriv θ Δ (n + α)| ≤ 2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := hb1
                _ ≤ 2 * Δ ^ 2 / (L ^ 2 / 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
                _ = 8 * Δ ^ 2 / L ^ 2 := by ring
                _ ≤ 16 * Δ ^ 2 / L ^ 2 := by gcongr; norm_num
            have hsb := sincPi_bound ((x + Complex.I * y) - n - α)
            have hs1 : ‖sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤ Real.exp (2 * Real.pi * R + 4) := by
              rw [norm_pow]
              calc ‖sincPi _‖ ^ 2 ≤ (Real.exp (Real.pi * R + 2)) ^ 2 := by
                    gcongr; exact hsb.1.trans (Real.exp_le_exp.mpr (by gcongr))
                _ = Real.exp (2 * Real.pi * R + 4) := by rw [← Real.exp_nat_mul]; ring_nf
            have hs2 : ‖((x + Complex.I * y) - n - α) * sincPi ((x + Complex.I * y) - n - α) ^ 2‖ ≤
                Real.exp (2 * Real.pi * R + 4) := hsb.2.trans (Real.exp_le_exp.mpr (by gcongr))
            dsimp only [term_z]
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc ((rescaledFDeriv θ Δ (n + α) : ℝ) : ℂ),
              norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hf_eq : f_near n = (32 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4) := by simp [f_near, h_mem]
            have hff_nn : 0 ≤ f_far n := by dsimp only [f_far]; positivity
            calc |rescaledF θ Δ (n + α)| * _ + |rescaledFDeriv θ Δ (n + α)| * _
                ≤ (16 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4) +
                  (16 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4) := by gcongr
              _ = f_near n := by rw [hf_eq]; ring
              _ ≤ f_far n + f_near n := by linarith
        have h_fn_sum : ∑' n : ℤ, f_near n ≤ 192 * Δ ^ 2 * Real.exp (2 * Real.pi * R + 4) / L := by
          rw [tsum_eq_sum (s := F_near) (fun n hn => by simp [f_near, hn])]
          rw [Finset.sum_congr rfl (fun n hn => by simp [f_near, hn]), Finset.sum_const, nsmul_eq_mul]
          have hcard : (F_near.card : ℝ) ≤ 6 * L := by
            have h1 : (F_near.card : ℤ) = 2 * Int.ceil (2 * L) + 1 := by
              dsimp only [F_near]; rw [Int.card_Icc]; omega
            have h2 : (F_near.card : ℝ) = 2 * (Int.ceil (2 * L) : ℝ) + 1 := by exact_mod_cast h1
            have h3 : (Int.ceil (2 * L) : ℝ) < 2 * L + 1 := Int.ceil_lt_add_one (2 * L)
            linarith
          calc (F_near.card : ℝ) * ((32 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4))
              ≤ (6 * L) * ((32 * Δ ^ 2 / L ^ 2) * Real.exp (2 * Real.pi * R + 4)) := by gcongr
            _ = 192 * Δ ^ 2 * Real.exp (2 * Real.pi * R + 4) / L := by field_simp [hL_pos.ne']; ring
        have h_ff_sum : ∑' n : ℤ, f_far n = 4 * (S_a + S_b) * Real.exp (2 * Real.pi * R + 4) / L := by
          have h_eq : f_far = fun n => (4 * Real.exp (2 * Real.pi * R + 4) / L) * (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|) := by
            ext n; dsimp only [f_far]; ring
          rw [h_eq, tsum_mul_left, Summable.tsum_add ha_summ hb_summ]
          dsimp only [S_a, S_b]; ring
        calc ‖∑' n : ℤ, term_z n‖ ≤ ∑' n : ℤ, ‖term_z n‖ := norm_tsum_le_tsum_norm h_s_tz.norm
          _ ≤ ∑' n : ℤ, (f_far n + f_near n) := Summable.tsum_le_tsum h_term_le h_s_tz.norm (hf_far_s.add hf_near_s)
          _ = (∑' n : ℤ, f_far n) + (∑' n : ℤ, f_near n) := Summable.tsum_add hf_far_s hf_near_s
          _ ≤ 4 * (S_a + S_b) * Real.exp (2 * Real.pi * R + 4) / L +
              192 * Δ ^ 2 * Real.exp (2 * Real.pi * R + 4) / L := by linarith
          _ = C_v / L := by dsimp only [C_v]; ring
      have h_horiz_bd : ∀ L : ℝ, 0 ≤ L →
          ‖∫ x in (-L)..L, g (x + Complex.I * (s * R))‖ ≤ (S_a + S_bm) / (Real.pi * R) := by
        intro L hL
        refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : -L ≤ L)).trans ?_
        let g_dom : ℤ → ℝ → ℝ := fun n x =>
          (|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / ((x - n - α) ^ 2 + R ^ 2)) +
          (|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) *
            ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2)
        have hg_dom_int : ∀ n : ℤ, Integrable (g_dom n) := by
          intro n
          have h1 : Integrable (fun x : ℝ => 1 / ((x - n - α) ^ 2 + R ^ 2)) := by
            have heq : (fun x : ℝ => 1 / ((x - n - α) ^ 2 + R ^ 2)) =
                fun x : ℝ => (1 / R ^ 2) * (1 / (1 + ((x - (n + α)) / R) ^ 2)) := by
              ext x; field_simp [hR_pos.ne']; ring
            rw [heq]
            exact ((integrable_inv_one_add_sq.comp_div hR_pos.ne').comp_sub_right (n + α)).const_mul _
          have h2 : Integrable (fun x : ℝ => 1 / (x ^ 2 + R ^ 2)) := by
            have heq : (fun x : ℝ => 1 / (x ^ 2 + R ^ 2)) =
                fun x : ℝ => (1 / R ^ 2) * (1 / (1 + (x / R) ^ 2)) := by
              ext x; field_simp [hR_pos.ne']; ring
            rw [heq]
            exact (integrable_inv_one_add_sq.comp_div hR_pos.ne').const_mul _
          exact (h1.const_mul _).add (((h2.add h1).div_const 2).const_mul _)
        have hg_dom_int_val : ∀ n : ℤ, ∫ x : ℝ, g_dom n x =
            (|rescaledF θ Δ (n + α)| + |(n + α) * rescaledFDeriv θ Δ (n + α)|) / (Real.pi * R) := by
          intro n
          have hi1 : ∫ x : ℝ, 1 / ((x - n - α) ^ 2 + R ^ 2) = Real.pi / R := by
            simpa [sub_sub] using integral_inv_add_sq_R (c := (n : ℝ) + α) hR_pos
          have hi2 : ∫ x : ℝ, 1 / (x ^ 2 + R ^ 2) = Real.pi / R := by
            simpa using integral_inv_add_sq_R (c := 0) hR_pos
          dsimp only [g_dom]
          have h_i1 : Integrable (fun x : ℝ => 1 / ((x - n - α) ^ 2 + R ^ 2)) := by
            have heq : (fun x : ℝ => 1 / ((x - n - α) ^ 2 + R ^ 2)) =
                fun x : ℝ => (1 / R ^ 2) * (1 / (1 + ((x - (n + α)) / R) ^ 2)) := by
              ext x; field_simp [hR_pos.ne']; ring
            rw [heq]
            exact ((integrable_inv_one_add_sq.comp_div hR_pos.ne').comp_sub_right (n + α)).const_mul _
          have h_i2 : Integrable (fun x : ℝ => 1 / (x ^ 2 + R ^ 2)) := by
            have heq : (fun x : ℝ => 1 / (x ^ 2 + R ^ 2)) =
                fun x : ℝ => (1 / R ^ 2) * (1 / (1 + (x / R) ^ 2)) := by
              ext x; field_simp [hR_pos.ne']; ring
            rw [heq]
            exact (integrable_inv_one_add_sq.comp_div hR_pos.ne').const_mul _
          rw [integral_add (h_i1.const_mul _) (((h_i2.add h_i1).div_const 2).const_mul _),
            integral_const_mul, integral_const_mul, integral_div, integral_add h_i2 h_i1, hi1, hi2]
          field_simp [Real.pi_ne_zero, hR_pos.ne']; ring
        have hg_summ_int : ∑' n : ℤ, ∫⁻ x : ℝ, ‖g_dom n x‖ₑ < ⊤ := by
          have h_eq : (fun n : ℤ => ∫⁻ x : ℝ, ‖g_dom n x‖ₑ) = fun n : ℤ => ENNReal.ofReal (∫ x : ℝ, g_dom n x) := by
            ext n
            rw [← ofReal_integral_eq_lintegral_ofReal (hg_dom_int n) (Eventually.of_forall fun x => by dsimp only [g_dom]; positivity)]
            congr 1; ext x; dsimp only [g_dom]; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
          rw [h_eq]
          have hs_real : Summable (fun n : ℤ => ∫ x : ℝ, g_dom n x) := by
            simp_rw [hg_dom_int_val]
            exact ((ha_summ.add hbm_summ).div_const (Real.pi * R))
          have h_tsum_le : ∑' n : ℤ, ENNReal.ofReal (∫ x : ℝ, g_dom n x) ≤
              ENNReal.ofReal (∑' n : ℤ, ∫ x : ℝ, g_dom n x) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by rw [hg_dom_int_val]; positivity) hs_real]
          exact h_tsum_le.trans_lt ENNReal.ofReal_lt_top
        have h_tot_int : Integrable (fun x : ℝ => ∑' n : ℤ, g_dom n x) :=
          integrable_tsum (fun n => (hg_dom_int n).aestronglyMeasurable) hg_summ_int.ne
        have h_tot_val : ∫ x : ℝ, (∑' n : ℤ, g_dom n x) = (S_a + S_bm) / (Real.pi * R) := by
          rw [integral_tsum (fun n => (hg_dom_int n).aestronglyMeasurable) hg_summ_int.ne]
          simp_rw [hg_dom_int_val, div_eq_mul_one_div, tsum_mul_right, Summable.tsum_add ha_summ hbm_summ]
          dsimp only [S_a, S_bm]; ring
        have h_pt_bd : ∀ x : ℝ, ‖g (x + Complex.I * (s * R))‖ ≤ ∑' n : ℤ, g_dom n x := by
          intro x
          let z : ℂ := x + Complex.I * (s * R)
          have hz_ne : z ≠ 0 := by
            intro h0; have him := congr_arg Complex.im h0
            simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add] at him
            have : |s * R| = 0 := by rw [him, abs_zero]
            rw [abs_mul, hs_abs, one_mul, abs_of_pos hR_pos] at this
            linarith
          have hzna_ne : ∀ n : ℤ, z - n - α ≠ 0 := by
            intro n h0; have him := congr_arg Complex.im h0
            simp only [z, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add, Complex.intCast_im, sub_zero] at him
            have : |s * R| = 0 := by rw [him, abs_zero]
            rw [abs_mul, hs_abs, one_mul, abs_of_pos hR_pos] at this
            linarith
          have hexp_bd : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * z)‖ ≤ Real.exp (-2 * Real.pi * R) := by
            rw [Complex.norm_exp]
            refine Real.exp_le_exp.mpr ?_
            have hre : (-2 * (Real.pi : ℂ) * Complex.I * ξ * z).re = 2 * Real.pi * ξ * s * R := by
              dsimp only [z]
              simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; ring
            rw [hre, show 2 * Real.pi * ξ * s * R = 2 * Real.pi * (ξ * s) * R by ring, hξs]
            nlinarith [Real.pi_pos]
          have h_sin_eq : ∀ n : ℤ, Complex.sin (Real.pi * (z - n - α)) ^ 2 = Complex.sin (Real.pi * (z - α)) ^ 2 := by
            intro n
            have h1 : Real.pi * (z - α) = Real.pi * (z - n - α) + (n : ℂ) * Real.pi := by ring
            rw [h1, Complex.sin_add_int_mul_pi]
            simp [mul_pow, ← pow_mul, mul_comm n 2]
          have h_sin_n : ‖Complex.sin (Real.pi * (z - α)) ^ 2‖ ≤ Real.exp (2 * Real.pi * R) := by
            rw [norm_pow]
            have him : |(Real.pi * (z - α)).im| = Real.pi * R := by
              have h1 : (Real.pi * (z - α)).im = Real.pi * (s * R) := by
                dsimp only [z]; simp [Complex.mul_im, Complex.sub_im, Complex.add_im]
              rw [h1, abs_mul, abs_of_pos Real.pi_pos, abs_mul, hs_abs, one_mul, abs_of_pos hR_pos]
            calc ‖Complex.sin (Real.pi * (z - α))‖ ^ 2 ≤ Real.exp (Real.pi * R) ^ 2 := by
                  gcongr; exact (h_sin_bd _).trans_eq (by rw [him])
              _ = Real.exp (2 * Real.pi * R) := by rw [← Real.exp_nat_mul]; ring_nf
          have h_sa : Summable (fun n : ℤ => (rescaledF θ Δ (n + α) : ℂ) * sincPi (z - n - α) ^ 2) := by
            refine (ha_summ.mul_right (Real.exp (2 * Real.pi * R + 4))).of_norm_bounded fun n => ?_
            have hsb := sincPi_bound (z - n - α)
            have him : |(z - n - α).im| = R := by
              dsimp only [z]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, abs_mul, hs_abs, abs_of_pos hR_pos]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
            have hs1 : ‖sincPi (z - n - α)‖ ^ 2 ≤ Real.exp (2 * Real.pi * R + 4) := by
              calc ‖sincPi _‖ ^ 2 ≤ Real.exp (Real.pi * R + 2) ^ 2 := by gcongr; exact hsb.1.trans_eq (by rw [him])
                _ = Real.exp (2 * Real.pi * R + 4) := by rw [← Real.exp_nat_mul]; ring_nf
            exact mul_le_mul_of_nonneg_left hs1 (abs_nonneg _)
          have h_sb : Summable (fun n : ℤ => (rescaledFDeriv θ Δ (n + α) : ℂ) * (z - n - α) * sincPi (z - n - α) ^ 2) := by
            refine (hb_summ.mul_right (Real.exp (2 * Real.pi * R + 4))).of_norm_bounded fun n => ?_
            have hsb := sincPi_bound (z - n - α)
            have him : |(z - n - α).im| = R := by
              dsimp only [z]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, abs_mul, hs_abs, abs_of_pos hR_pos]
            rw [mul_assoc ((rescaledFDeriv θ Δ (n + α) : ℝ) : ℂ), norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hsb.2.trans_eq (by rw [him])) (abs_nonneg _)
          have h_sb_eq : ∑' n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) * (z - n - α) * sincPi (z - n - α) ^ 2 =
              (Complex.sin (Real.pi * (z - α)) ^ 2 / Real.pi ^ 2) *
                ∑' n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α)) := by
            have h_each : ∀ n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) * (z - n - α) * sincPi (z - n - α) ^ 2 =
                (Complex.sin (Real.pi * (z - α)) ^ 2 / Real.pi ^ 2) * ((rescaledFDeriv θ Δ (n + α) : ℂ) / (z - n - α)) := by
              intro n; dsimp only [sincPi]; simp only [if_neg (hzna_ne n), div_pow, h_sin_eq n]
              have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
              field_simp [hpi, hzna_ne n]; ring
            simp_rw [h_each, tsum_mul_left]
            congr 1
            have h_id : ∀ n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) / (z - n - α) =
                (rescaledFDeriv θ Δ (n + α) : ℂ) / z +
                (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α)) := by
              intro n; field_simp [hz_ne, hzna_ne n]; ring
            have h_s1 : Summable (fun n : ℤ => (rescaledFDeriv θ Δ (n + α) : ℂ) / z) :=
              (hsumm_b.ofReal).div_const z
            have h_s2 : Summable (fun n : ℤ => (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α))) := by
              refine (hbm_summ.mul_left (1 / R ^ 2)).of_norm_bounded fun n => ?_
              rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul,
                norm_mul]
              have hz_r : R ≤ ‖z‖ := by
                have hsq : R ^ 2 ≤ ‖z‖ ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
                  simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
                    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
                    one_mul, zero_add]
                  have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                  nlinarith [sq_nonneg x]
                exact (sq_le_sq₀ hR_pos.le (norm_nonneg _)).mp hsq
              have hzna_r : R ≤ ‖z - n - α‖ := by
                have hsq : R ^ 2 ≤ ‖z - n - α‖ ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
                  simp only [z, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
                    Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add, Complex.intCast_im, sub_zero]
                  have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                  nlinarith [sq_nonneg ((x : ℝ) - n - α)]
                exact (sq_le_sq₀ hR_pos.le (norm_nonneg _)).mp hsq
              rw [mul_comm (rescaledFDeriv θ Δ (n + α))]
              calc |(n + α) * rescaledFDeriv θ Δ (n + α)| / (‖z‖ * ‖z - n - α‖)
                  ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| / (R * R) :=
                    div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (mul_le_mul hz_r hzna_r hR_pos.le (norm_nonneg _))
                _ = (1 / R ^ 2) * |(n + α) * rescaledFDeriv θ Δ (n + α)| := by ring
            simp_rw [h_id, Summable.tsum_add h_s1 h_s2, tsum_div_const]
            have h0 : ∑' n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) = 0 := by
              rw [← Complex.ofReal_tsum, hsum0, Complex.ofReal_zero]
            rw [h0, zero_div, zero_add]
          have h_norm_M : ‖M_α z‖ ≤ Real.exp (2 * Real.pi * R) * ∑' n : ℤ, g_dom n x := by
            rw [hMα_eq z, Summable.tsum_add h_sa h_sb, h_sb_eq]
            refine (norm_add_le _ _).trans ?_
            have h_p1 : ‖∑' n : ℤ, (rescaledF θ Δ (n + α) : ℂ) * sincPi (z - n - α) ^ 2‖ ≤
                Real.exp (2 * Real.pi * R) * ∑' n : ℤ, (|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / ((x - n - α) ^ 2 + R ^ 2)) := by
              rw [← tsum_mul_left]
              refine (norm_tsum_le_tsum_norm h_sa.norm).trans ?_
              refine Summable.tsum_le_tsum (fun n => ?_) h_sa.norm ?_
              · dsimp only [sincPi]; simp only [if_neg (hzna_ne n), div_pow, h_sin_eq n]
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_pow,
                  Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
                have hden : ‖z - n - α‖ ^ 2 = (x - n - α) ^ 2 + R ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
                  simp only [z, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                    zero_mul, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.intCast_re,
                    Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul, zero_add, Complex.intCast_im, sub_zero]
                  have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                  linarith
                calc |rescaledF θ Δ (n + α)| * (‖Complex.sin (Real.pi * (z - α)) ^ 2‖ / (Real.pi ^ 2 * ‖z - n - α‖ ^ 2))
                    ≤ |rescaledF θ Δ (n + α)| * (Real.exp (2 * Real.pi * R) / (Real.pi ^ 2 * ((x - n - α) ^ 2 + R ^ 2))) := by
                      rw [hden]; gcongr
                  _ = _ := by ring
              · refine (ha_summ.mul_left (Real.exp (2 * Real.pi * R) / (Real.pi ^ 2 * R ^ 2))).of_nonneg_of_le
                  (fun _ => by positivity) (fun n => ?_)
                have : R ^ 2 ≤ (x - n - α) ^ 2 + R ^ 2 := by linarith [sq_nonneg (x - n - α)]
                calc Real.exp (2 * Real.pi * R) * ((|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / ((x - n - α) ^ 2 + R ^ 2)))
                    ≤ Real.exp (2 * Real.pi * R) * ((|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / R ^ 2)) := by gcongr
                  _ = _ := by ring
            have h_p2 : ‖(Complex.sin (Real.pi * (z - α)) ^ 2 / Real.pi ^ 2) *
                ∑' n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α))‖ ≤
                Real.exp (2 * Real.pi * R) * ∑' n : ℤ, (|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) *
                  ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2) := by
              rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos Real.pi_pos),
                ← tsum_mul_left]
              have h_s_inner : Summable (fun n : ℤ => (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α))) := by
                refine (hbm_summ.mul_left (1 / R ^ 2)).of_norm_bounded fun n => ?_
                rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  ← abs_mul, norm_mul, mul_comm (rescaledFDeriv θ Δ (n + α))]
                have hz_r : R ≤ ‖z‖ := by
                  have hsq : R ^ 2 ≤ ‖z‖ ^ 2 := by
                    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]
                    have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                    nlinarith [sq_nonneg x]
                  exact (sq_le_sq₀ hR_pos.le (norm_nonneg _)).mp hsq
                have hzna_r : R ≤ ‖z - n - α‖ := by
                  have hsq : R ^ 2 ≤ ‖z - n - α‖ ^ 2 := by
                    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]
                    have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                    nlinarith [sq_nonneg ((x : ℝ) - n - α)]
                  exact (sq_le_sq₀ hR_pos.le (norm_nonneg _)).mp hsq
                calc |(n + α) * rescaledFDeriv θ Δ (n + α)| / (‖z‖ * ‖z - n - α‖)
                    ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| / (R * R) :=
                      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (mul_le_mul hz_r hzna_r hR_pos.le (norm_nonneg _))
                  _ = _ := by ring
              have h_amgm : ∀ n : ℤ, ‖(rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α))‖ ≤
                  |(n + α) * rescaledFDeriv θ Δ (n + α)| * ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2) := by
                intro n
                rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  ← abs_mul, norm_mul, mul_comm (rescaledFDeriv θ Δ (n + α))]
                have hz2 : ‖z‖ ^ 2 = x ^ 2 + R ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]
                  have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                  linarith
                have hzna2 : ‖z - n - α‖ ^ 2 = (x - n - α) ^ 2 + R ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]
                  have hs2 : (s * R) ^ 2 = R ^ 2 := by rw [mul_pow, ← sq_abs s, hs_abs]; ring
                  linarith
                have h_ineq : 2 * (1 / ‖z‖) * (1 / ‖z - n - α‖) ≤ 1 / ‖z‖ ^ 2 + 1 / ‖z - n - α‖ ^ 2 := by
                  have : (1 / ‖z‖ - 1 / ‖z - n - α‖) ^ 2 ≥ 0 := sq_nonneg _
                  nlinarith [show (1 / ‖z‖) ^ 2 = 1 / ‖z‖ ^ 2 by ring,
                    show (1 / ‖z - n - α‖) ^ 2 = 1 / ‖z - n - α‖ ^ 2 by ring]
                rw [hz2, hzna2] at h_ineq
                calc |(n + α) * rescaledFDeriv θ Δ (n + α)| / (‖z‖ * ‖z - n - α‖)
                    = |(n + α) * rescaledFDeriv θ Δ (n + α)| * ((1 / ‖z‖) * (1 / ‖z - n - α‖)) := by ring
                  _ ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| * ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2) := by
                      gcongr; linarith
              have h_s_amgm : Summable (fun n : ℤ => |(n + α) * rescaledFDeriv θ Δ (n + α)| *
                  ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2)) := by
                refine (hbm_summ.mul_left (1 / R ^ 2)).of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
                have h1 : 1 / (x ^ 2 + R ^ 2) ≤ 1 / R ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_nonneg x])
                have h2 : 1 / ((x - n - α) ^ 2 + R ^ 2) ≤ 1 / R ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_nonneg (x - n - α)])
                nlinarith [abs_nonneg ((n + α) * rescaledFDeriv θ Δ (n + α))]
              calc (‖Complex.sin (Real.pi * (z - α)) ^ 2‖ / Real.pi ^ 2) *
                    ‖∑' n : ℤ, (rescaledFDeriv θ Δ (n + α) : ℂ) * ((n + α : ℝ) : ℂ) / (z * (z - n - α))‖
                  ≤ (Real.exp (2 * Real.pi * R) / Real.pi ^ 2) *
                      ∑' n : ℤ, |(n + α) * rescaledFDeriv θ Δ (n + α)| *
                        ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2) := by
                    gcongr
                    exact (norm_tsum_le_tsum_norm h_s_inner.norm).trans
                      (Summable.tsum_le_tsum h_amgm h_s_inner.norm h_s_amgm)
                _ = ∑' n : ℤ, Real.exp (2 * Real.pi * R) *
                      ((|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) *
                        ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2)) := by
                    rw [← tsum_mul_left]; congr 1; ext n; ring
            have h_s1' : Summable (fun n : ℤ => Real.exp (2 * Real.pi * R) *
                ((|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / ((x - n - α) ^ 2 + R ^ 2)))) := by
              refine (ha_summ.mul_left (Real.exp (2 * Real.pi * R) / (Real.pi ^ 2 * R ^ 2))).of_nonneg_of_le
                (fun _ => by positivity) (fun n => ?_)
              have : R ^ 2 ≤ (x - n - α) ^ 2 + R ^ 2 := by linarith [sq_nonneg (x - n - α)]
              calc Real.exp (2 * Real.pi * R) * ((|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / ((x - n - α) ^ 2 + R ^ 2)))
                  ≤ Real.exp (2 * Real.pi * R) * ((|rescaledF θ Δ (n + α)| / Real.pi ^ 2) * (1 / R ^ 2)) := by gcongr
                _ = _ := by ring
            have h_s2' : Summable (fun n : ℤ => Real.exp (2 * Real.pi * R) *
                ((|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) *
                  ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2))) := by
              refine (hbm_summ.mul_left (Real.exp (2 * Real.pi * R) / (Real.pi ^ 2 * R ^ 2))).of_nonneg_of_le
                (fun _ => by positivity) (fun n => ?_)
              have h1 : 1 / (x ^ 2 + R ^ 2) ≤ 1 / R ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_nonneg x])
              have h2 : 1 / ((x - n - α) ^ 2 + R ^ 2) ≤ 1 / R ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_nonneg (x - n - α)])
              have hb_nn : 0 ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| := abs_nonneg _
              calc Real.exp (2 * Real.pi * R) * ((|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) *
                    ((1 / (x ^ 2 + R ^ 2) + 1 / ((x - n - α) ^ 2 + R ^ 2)) / 2))
                  ≤ Real.exp (2 * Real.pi * R) * ((|(n + α) * rescaledFDeriv θ Δ (n + α)| / Real.pi ^ 2) * (1 / R ^ 2)) := by
                    gcongr; linarith
                _ = _ := by ring
            calc _ ≤ _ := add_le_add h_p1 h_p2
              _ = Real.exp (2 * Real.pi * R) * ∑' n : ℤ, g_dom n x := by
                  rw [← Summable.tsum_add h_s1' h_s2', ← tsum_mul_left]
                  congr 1; ext n; dsimp only [g_dom]; ring
          dsimp only [g]
          rw [norm_mul]
          calc ‖M_α (x + Complex.I * (s * R))‖ * ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * (x + Complex.I * (s * R)))‖
              ≤ (Real.exp (2 * Real.pi * R) * ∑' n : ℤ, g_dom n x) * Real.exp (-2 * Real.pi * R) :=
                mul_le_mul h_norm_M hexp_bd (norm_nonneg _) (by positivity)
            _ = ∑' n : ℤ, g_dom n x := by
                rw [mul_assoc, mul_comm (∑' n : ℤ, g_dom n x), ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        calc ∫ x in (-L)..L, ‖g (x + Complex.I * (s * R))‖
            ≤ ∫ x in (-L)..L, ∑' n : ℤ, g_dom n x := by
              rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
              exact setIntegral_mono_on ((hg_diff.continuous.comp (by fun_prop)).norm.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
                h_tot_int.integrableOn measurableSet_Ioc (fun x _ => h_pt_bd x)
          _ ≤ ∫ x : ℝ, ∑' n : ℤ, g_dom n x := by
              rw [intervalIntegral.integral_of_le (by linarith)]
              exact setIntegral_le_integral h_tot_int (Eventually.of_forall fun x => tsum_nonneg fun n => by dsimp only [g_dom]; positivity)
          _ = (S_a + S_bm) / (Real.pi * R) := h_tot_val
      have h_fourier_eq : 𝓕 f ξ = ∫ x : ℝ, g x := by
        rw [Real.fourierIntegral_eq_integral_exp_smul]
        congr 1; ext x
        dsimp only [f, g]
        rw [hMα_real x, smul_eq_mul, mul_comm]
        congr 2
        push_cast; ring
      have h_rect : ∀ L : ℝ, 2 * Δ ≤ L →
          ‖∫ x in (-L)..L, g x‖ ≤ (S_a + S_bm) / (Real.pi * R) + 2 * R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L := by
        intro L hL
        have h_cauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g (-L : ℂ) (L + Complex.I * (s * R))
          (hg_diff.differentiableOn)
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
          Complex.add_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, mul_one, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, one_mul, zero_add] at h_cauchy
        have h_sum : ∫ x in (-L)..L, g x =
            (∫ x in (-L)..L, g (x + Complex.I * (s * R))) -
            Complex.I * (∫ y in (0 : ℝ)..(s * R), g (L + Complex.I * y)) +
            Complex.I * (∫ y in (0 : ℝ)..(s * R), g (-L + Complex.I * y)) := by
          have h_c : (∫ x in (-L)..L, g x) - (∫ x in (-L)..L, g (x + Complex.I * (s * R))) +
              Complex.I * (∫ y in (0 : ℝ)..(s * R), g (L + Complex.I * y)) -
              Complex.I * (∫ y in (0 : ℝ)..(s * R), g (-L + Complex.I * y)) = 0 := by
            simpa [mul_comm Complex.I] using h_cauchy
          exact eq_of_sub_eq_zero (by linear_combination h_c)
        rw [h_sum]
        have h_v1 : ‖Complex.I * ∫ y in (0 : ℝ)..(s * R), g (L + Complex.I * y)‖ ≤
            R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L := by
          rw [norm_mul, Complex.norm_I, one_mul]
          refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_).trans ?_
          · have hy_abs : |y| ≤ R := by
              have hsr : |s * R| ≤ R := by rw [abs_mul, hs_abs, one_mul, abs_of_pos hR_pos]
              rw [Set.mem_uIoc] at hy
              rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;>
                [exact ⟨by linarith [(abs_le.mp hsr).1], by linarith [(abs_le.mp hsr).2]⟩;
                 exact ⟨by linarith [(abs_le.mp hsr).1], by linarith [(abs_le.mp hsr).2]⟩]
            have hexp : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * (L + Complex.I * y))‖ ≤ Real.exp (2 * Real.pi * |ξ| * R) := by
              rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_
              have hre : (-2 * (Real.pi : ℂ) * Complex.I * ξ * (L + Complex.I * y)).re = 2 * Real.pi * ξ * y := by
                simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; ring
              rw [hre]
              calc 2 * Real.pi * ξ * y ≤ |2 * Real.pi * ξ * y| := le_abs_self _
                _ = 2 * Real.pi * |ξ| * |y| := by rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
                _ ≤ 2 * Real.pi * |ξ| * R := by gcongr
            dsimp only [g]; rw [norm_mul]
            exact mul_le_mul (h_vert_bd L hL L (abs_of_pos (by linarith)) y hy_abs) hexp (norm_nonneg _) (by positivity)
          · rw [sub_zero, abs_mul, hs_abs, one_mul, abs_of_pos hR_pos]; ring_nf; rfl
        have h_v2 : ‖Complex.I * ∫ y in (0 : ℝ)..(s * R), g (-L + Complex.I * y)‖ ≤
            R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L := by
          rw [norm_mul, Complex.norm_I, one_mul]
          refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_).trans ?_
          · have hy_abs : |y| ≤ R := by
              have hsr : |s * R| ≤ R := by rw [abs_mul, hs_abs, one_mul, abs_of_pos hR_pos]
              rw [Set.mem_uIoc] at hy
              rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;>
                [exact ⟨by linarith [(abs_le.mp hsr).1], by linarith [(abs_le.mp hsr).2]⟩;
                 exact ⟨by linarith [(abs_le.mp hsr).1], by linarith [(abs_le.mp hsr).2]⟩]
            have hexp : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * (-L + Complex.I * y))‖ ≤ Real.exp (2 * Real.pi * |ξ| * R) := by
              rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_
              have hre : (-2 * (Real.pi : ℂ) * Complex.I * ξ * (-L + Complex.I * y)).re = 2 * Real.pi * ξ * y := by
                simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; ring
              rw [hre]
              calc 2 * Real.pi * ξ * y ≤ |2 * Real.pi * ξ * y| := le_abs_self _
                _ = 2 * Real.pi * |ξ| * |y| := by rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
                _ ≤ 2 * Real.pi * |ξ| * R := by gcongr
            dsimp only [g]; rw [norm_mul]
            exact mul_le_mul (h_vert_bd L hL (-L) (by rw [abs_neg, abs_of_pos (by linarith)]) y hy_abs) hexp (norm_nonneg _) (by positivity)
          · rw [sub_zero, abs_mul, hs_abs, one_mul, abs_of_pos hR_pos]; ring_nf; rfl
        have h_hb := h_horiz_bd L (by linarith)
        calc ‖(∫ x in (-L)..L, g (x + Complex.I * (s * R))) -
              Complex.I * (∫ y in (0 : ℝ)..(s * R), g (L + Complex.I * y)) +
              Complex.I * (∫ y in (0 : ℝ)..(s * R), g (-L + Complex.I * y))‖
            ≤ ‖∫ x in (-L)..L, g (x + Complex.I * (s * R))‖ +
              ‖Complex.I * (∫ y in (0 : ℝ)..(s * R), g (L + Complex.I * y))‖ +
              ‖Complex.I * (∫ y in (0 : ℝ)..(s * R), g (-L + Complex.I * y))‖ :=
                (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
          _ ≤ (S_a + S_bm) / (Real.pi * R) + R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L +
              R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L := by linarith
          _ = (S_a + S_bm) / (Real.pi * R) + 2 * R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L := by ring
      have hg_int : Integrable (fun x : ℝ => g x) := by
        have h_eq : (fun x : ℝ => g x) = fun x : ℝ => f x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) := by
          ext x; dsimp only [f, g]; rw [hMα_real x]
        rw [h_eq]
        refine hf_int.bdd_mul ?_ (Eventually.of_forall fun x => ?_)
        · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
        · rw [show -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
      have h_tend1 : Tendsto (fun L : ℝ => ‖∫ x in (-L)..L, g x‖) atTop (nhds ‖𝓕 f ξ‖) := by
        rw [h_fourier_eq]
        exact (intervalIntegral_tendsto_integral hg_int tendsto_neg_atTop_atBot tendsto_id).norm
      have h_tend2 : Tendsto (fun L : ℝ => (S_a + S_bm) / (Real.pi * R) + 2 * R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L)
          atTop (nhds ((S_a + S_bm) / (Real.pi * R))) := by
        have h0 : Tendsto (fun L : ℝ => 2 * R * Real.exp (2 * Real.pi * |ξ| * R) * C_v / L) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        simpa using tendsto_const_nhds.add h0
      exact le_of_tendsto_of_tendsto h_tend1 h_tend2 ((eventually_ge_atTop (2 * Δ)).mono fun L hL => h_rect L hL)
    by_contra hne
    have h_pos : 0 < ‖𝓕 f ξ‖ := norm_pos_iff.mpr hne
    let R : ℝ := max 1 ((S_a + S_bm) / (Real.pi * ‖𝓕 f ξ‖) + 1)
    have h1 := h_rect_bd R (le_max_left _ _)
    have h2 : (S_a + S_bm) / (Real.pi * ‖𝓕 f ξ‖) < R := by linarith [le_max_right (1 : ℝ) ((S_a + S_bm) / (Real.pi * ‖𝓕 f ξ‖) + 1)]
    have hR_pos : 0 < R := by positivity
    rw [div_lt_iff₀ (mul_pos Real.pi_pos h_pos)] at h2
    rw [le_div_iff₀ (mul_pos Real.pi_pos hR_pos)] at h1
    linarith
  have hf'_decay : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * (1 + |ξ|) ^ (-2 : ℝ) := by
    let C₀ : ℝ := 4 * ∫ y : ℝ, ‖f y‖
    refine ⟨C₀, fun ξ => ?_⟩
    by_cases hξ : 1 ≤ |ξ|
    · rw [hf_fourier_zero ξ hξ, norm_zero]
      positivity
    · have hξ1 : |ξ| < 1 := not_le.mp hξ
      have h_f_bd : ‖𝓕 f ξ‖ ≤ ∫ y : ℝ, ‖f y‖ := by
        rw [Real.fourierIntegral_eq_integral_exp_smul]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        congr 1; ext y
        rw [norm_smul, show ‖Real.fourierChar (-ξ * y)‖ = 1 by
          rw [Real.fourierChar_apply, Circle.norm_coe]]
        ring
      have h_pos : 0 < 1 + |ξ| := by positivity
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg h_pos.le, Real.rpow_natCast]
      have hsq : (1 + |ξ|) ^ 2 ≤ 4 := by nlinarith
      calc ‖𝓕 f ξ‖ ≤ ∫ y : ℝ, ‖f y‖ := h_f_bd
        _ = C₀ / 4 := by dsimp only [C₀]; ring
        _ ≤ C₀ / (1 + |ξ|) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
        _ = C₀ * ((1 + |ξ|) ^ 2)⁻¹ := div_eq_mul_inv _ _
  have hpois := Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay hf_cont (by norm_num : (1 : ℝ) < 2) hf_decay hf'_decay α
  have h_lhs : (∑' n : ℤ, f (α + n)).re = ∑' n : ℤ, rescaledF θ Δ (n + α) := by
    have hs : Summable (fun n : ℤ => f (α + n)) := by
      have h_s : Summable (fun n : ℤ => rescaledF θ Δ (n + α)) :=
        ha_summ.of_norm_bounded (fun n => by rw [Real.norm_eq_abs])
      simpa [f, vaalerInterpolant, add_comm] using h_s.ofReal
    rw [Complex.re_tsum hs]
    congr 1; ext n
    dsimp only [f]
    rw [Complex.ofReal_re]
    unfold vaalerInterpolant
    rw [if_pos ⟨n, by ring⟩, add_comm]
  have h_rhs : (∑' k : ℤ, Real.fourierChar (k * α) • 𝓕 f k).re = ∫ y : ℝ, vaalerInterpolant θ Δ α y := by
    have h_only0 : ∀ k : ℤ, Real.fourierChar (k * α) • 𝓕 f k = if k = 0 then 𝓕 f 0 else 0 := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp
      · have hk1 : 1 ≤ |(k : ℝ)| := by
          have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
          exact_mod_cast this
        rw [if_neg hk, hf_fourier_zero k hk1, smul_zero]
    simp_rw [h_only0, tsum_ite_eq, Real.fourierIntegral_zero_eq_integral]
    dsimp only [f]
    rw [integral_ofReal, Complex.ofReal_re]
  rw [hpois] at h_lhs
  linarith

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
          have heq : 1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ)) =
              2 * z / (z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2) := by
            field_simp [hne1, hne2]; ring
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
                _ ≤ ((k + 1 : ℝ) / 2) ^ 2 := sq_le_sq' (by positivity) h_1d
                _ = (k + 1 : ℝ) ^ 2 / 4 := by ring
                _ ≤ (k + 1 : ℝ) ^ 2 / 2 := by gcongr; norm_num
            linarith
          calc 2 * ‖z‖ / ‖z ^ 2 - ((k + 1 : ℕ) : ℂ) ^ 2‖
              ≤ 2 * (1 + Δ) / ((k + 1 : ℝ) ^ 2 / 2) :=
                div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
            _ = 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2 := by ring
      have h_sum_k : ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ ≤
          (K0 : ℝ) * (2 / δ) + 4 * (1 + Δ) * C_z := by
        have h1 : ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ ≤
            ∑ k ∈ Finset.range N, (if k < K0 then 2 / δ else 0) +
            ∑ k ∈ Finset.range N, (4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun k _ => ?_
          refine (h_each_k k).trans ?_
          split_ifs <;> positivity
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
                rw [show (fun k : ℕ => 4 * (1 + Δ) / (k + 1 : ℝ) ^ 2) = fun k => (4 * (1 + Δ)) * (1 / (k + 1 : ℝ) ^ 2) by ext k; ring,
                  tsum_mul_left]
        linarith
      calc ‖1 / z + ∑ k ∈ Finset.range N, (1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ)))‖
          ≤ ‖1 / z‖ + ∑ k ∈ Finset.range N, ‖1 / (z + (k + 1 : ℕ)) + 1 / (z - (k + 1 : ℕ))‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_sum_le _ _) _)
        _ ≤ 1 / δ + ((K0 : ℝ) * (2 / δ) + 4 * (1 + Δ) * C_z) := add_le_add hz0 h_sum_k
        _ ≤ C_dom := by dsimp only [C_dom]; linarith
    obtain ⟨C_dom, hC_dom, h_dom⟩ := h_dom_bd
    have h_int_tend : Tendsto (fun N : ℕ => ∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) *
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((n + α : ℝ) : ℂ) - Complex.I * v))).im)
        atTop (nhds (∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im)) := by
      refine intervalIntegral.tendsto_integral_of_dominated_convergence (bound := fun _ => C_dom) ?_ ?_
        intervalIntegrable_const ?_
      · intro N
        refine (Complex.continuous_im.comp (continuous_const.mul (continuous_finset_sum _ fun n _ =>
          continuous_const.div (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)) fun v => ?_))).aestronglyMeasurable
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
      · intro N
        rw [ae_restrict_iff' (by simp : MeasurableSet (Set.uIoc 0 Δ))]
        filter_upwards with v hv
        rw [Set.uIoc_of_le hΔ_pos.le] at hv
        rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul, show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        exact h_dom N v ⟨hv.1.le, hv.2⟩
      · rw [ae_restrict_iff' (by simp : MeasurableSet (Set.uIoc 0 Δ))]
        have h_ae : ∀ᵐ v : ℝ ∂volume, v ∈ Set.Ioc 0 Δ → v ∈ Set.Ioo 0 Δ := by
          filter_upwards [ae_iff.mpr (by simp : volume {v : ℝ | v = Δ} = 0)] with v hv h1
          exact ⟨h1.1, lt_of_le_of_ne h1.2 hv⟩
        filter_upwards [h_ae] with v hv1 hv2
        rw [Set.uIoc_of_le hΔ_pos.le] at hv2
        exact (Complex.imCLM.continuousAt.comp ((continuousAt_const).mul continuousAt_id)).tendsto.comp
          (h_cot_lim v (hv1 hv2))
    have h_bd_tend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (n + α) / ((n + α) ^ 2 + Δ ^ 2))
        atTop (nhds (cot_fn Δ).re) := by
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
    have hG_0 : Tendsto G (𝓝[>] 0) (nhds (-2 * envelopeC θ)) := by
      have h_cont : ContinuousAt G 0 := by
        refine (Complex.imCLM.continuousAt.comp (continuousAt_const.mul ?_)).neg
        refine (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (h_slit 0 le_rfl)))).continuousAt.comp ?_
        fun_prop
      have hG_val : G 0 = -2 * envelopeC θ := by
        dsimp only [G]
        have heq : 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * (0 : ℝ))) =
            Complex.exp ((Real.log (2 * Real.cos θ) : ℂ) + Complex.I * θ) := by
          rw [mul_zero, add_zero, Complex.exp_add, Complex.ofReal_log (by positivity),
            show 2 * Complex.I * (θ : ℂ) = Complex.I * θ + Complex.I * θ by ring,
            Complex.exp_add]
          have hcos_def : Complex.cos (θ : ℂ) = (Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I)) / 2 := by
            unfold Complex.cos; ring_nf
          rw [← Complex.ofReal_cos, hcos_def]
          push_cast; rw [Complex.exp_mul_I, show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]; simp [Complex.cos_neg, Complex.sin_neg]
          ring_nf; simp [Complex.I_sq]; ring
        rw [heq, Complex.log_exp (by
          simp [Complex.add_im, Complex.mul_im]
          have := abs_lt.mp hθ; exact ⟨by linarith, by linarith⟩)]
        have hexp : Complex.exp (-Complex.I * θ) = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
          rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.exp_mul_I]
          simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
          ring
        rw [hexp]
        unfold envelopeC
        simp only [sub_mul, Complex.mul_add, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero]
        ring
      rw [← hG_val]
      exact h_cont.continuousWithinAt.tendsto
    have hG_inf : Tendsto G atTop (nhds 0) := by
      have h1 : Tendsto (fun v : ℝ => 1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) atTop (nhds 1) := by
        have h0 : Tendsto (fun v : ℝ => Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))) atTop (nhds 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have h_n : ∀ v : ℝ, ‖Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))‖ = Real.exp (-2 * Real.pi * v) := by
            intro v; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.add_re]; ring
          simp_rw [h_n]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by positivity : -2 * Real.pi < 0))
        simpa using tendsto_const_nhds.add h0
      have h_log1 : Tendsto (fun v : ℝ => Complex.log (1 + Complex.exp (2 * Complex.I * (θ + Complex.I * Real.pi * v))))
          atTop (nhds 0) := by
        have hc := (Complex.hasDerivAt_log (by norm_num : (1 : ℂ) ∈ Complex.slitPlane)).continuousAt.tendsto.comp h1
        simpa [Complex.log_one] using hc
      simpa [G] using (Complex.imCLM.continuousAt.tendsto.comp (tendsto_const_nhds.mul h_log1)).neg
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hG_deriv h_int_r hG_0 hG_inf
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
        ring
        push_cast; ring_nf; simp [Complex.I_sq]; ring
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
      · exact ((h_int_cot.sub (h_int_pi.add h_int_rem |>.congr_fun (fun v _ => by
          rw [h_cot_star_eq v, mul_add, Complex.add_im]) measurableSet_uIcc)).1.norm).integrableOn
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
      have h_d : ∀ v ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * t))
          (Real.exp (-2 * Real.pi * v)) v := by
        intro v _
        have hd := ((hasDerivAt_id v).const_mul (-2 * Real.pi)).exp.const_mul (-(1 / (2 * Real.pi)))
        refine hd.congr_deriv ?_; field_simp [Real.pi_ne_zero]; ring
      simpa using integral_Ioi_of_hasDerivAt_of_tendsto' h_d h_int h_lim
    rw [integral_const_mul, h_val] at h_mono2
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
    rw [show (-2 * Real.pi * Δ : ℝ) = -(2 * Real.pi * Δ) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h1.trans_eq (one_mul _).symm
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
      ≤ |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
          (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))| +
        |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im) -
          (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)| +
        |Real.sin θ * Δ * (cot_fn Δ).re| := by
          have h1 := abs_sub_le (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) - Real.sin θ * Δ * (cot_fn Δ).re)
            (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im)) (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)
          have h2 : |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) - Real.sin θ * Δ * (cot_fn Δ).re -
              (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))| ≤
              |-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
                (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))| +
              |Real.sin θ * Δ * (cot_fn Δ).re| := by
            rw [show -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) - Real.sin θ * Δ * (cot_fn Δ).re -
                (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im)) =
                (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_fn v).im) -
                  (-(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) * cot_star v).im))) -
                Real.sin θ * Δ * (cot_fn Δ).re by ring]
            exact abs_sub _ _
          linarith
    _ ≤ (Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * (1 / (2 * Real.pi)) +
        (2 * Real.pi / Real.cos θ) * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) +
        Δ * ((Real.pi ^ 2 / c_sin ^ 2) * |α - α_star| * Real.exp (-2 * Real.pi * Δ) +
          (2 * Real.pi / Real.cos θ) * Real.exp (-2 * Real.pi * Δ)) := by
          rw [h_int_sub, abs_neg, h_cot_star_split]
          have h_s2 : |(-Real.pi * Δ * Real.cos θ + ∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) -
              (-Real.pi * Δ * Real.cos θ + 2 * envelopeC θ)| =
              |(∫ v in (0 : ℝ)..Δ, -(Complex.exp (-Complex.I * θ) * rem_fn v).im) - 2 * envelopeC θ| := by
            congr 1; ring
          rw [h_s2]
          linarith
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
          dsimp only [C_eval]
          nlinarith [mul_nonneg (div_nonneg (sq_nonneg Real.pi) (sq_nonneg c_sin)) h_pos1,
            mul_nonneg (div_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) hcos_pos.le) h_pos2]

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
    rw [show (-2 * Real.pi * Δ : ℝ) = -(2 * Real.pi * Δ) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h1.trans_eq (one_mul _).symm
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
        have h_2 : C_err1 * (1 + C_α) / c'_J ≤ Δ := by
          have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          linarith
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
        have h_2 : C_err1 * (1 + C_α) / (c_J / 2) ≤ Δ := by
          have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          linarith
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
          ext x; simp [Homeomorph.coe_neg]
        have h1 : ∫ x in Set.Iio (0 : ℝ), fV (Δ * x) = ∫ x in Set.Ioi (0 : ℝ), fV (-(Δ * x)) := by
          rw [← (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb (fun x => fV (Δ * x)) (Set.Iio 0)]
          have h_pre' : Neg.neg ⁻¹' Set.Iio (0 : ℝ) = Set.Ioi 0 := h_pre
          rw [h_pre']; congr 1; ext x; simp [mul_neg]
        have h2 : ∫ y in Set.Iio (0 : ℝ), fV y = ∫ y in Set.Ioi (0 : ℝ), fV (-y) := by
          rw [← (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb fV (Set.Iio 0)]
          have h_pre' : Neg.neg ⁻¹' Set.Iio (0 : ℝ) = Set.Ioi 0 := h_pre
          rw [h_pre']; rfl
        have h3 := MeasureTheory.integral_comp_mul_left_Ioi (fun y : ℝ => fV (-y)) (0 : ℝ) hΔ_pos
        rw [mul_zero, smul_eq_mul, inv_eq_one_div] at h3
        rw [h1, h2, ← h3]; congr 1; ext x; simp [mul_neg]
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
        ≤ (1 / Δ) * (C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - α_star|)) := by gcongr
      _ ≤ (1 / Δ) * (C_eval * (Δ * Real.exp (-2 * Real.pi * Δ) + C_α * Δ * Real.exp (-2 * Real.pi * Δ))) := by gcongr
      _ = C_err * Real.exp (-2 * Real.pi * Δ) := by
          dsimp only [C_err]; field_simp [hΔ_pos.ne']
  exact ⟨α, majorantEntire θ Δ α, hα_mem, hM_type, hM_re, h_int_diff, h_sup, h_L1, h_ge_K, h_excess⟩

end PolarEvaluation
