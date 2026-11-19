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

end PolarEvaluation
