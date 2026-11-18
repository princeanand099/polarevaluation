import PolarEvaluation.ShiftedLatticeShift

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

lemma summable_inv_add_sq_of_ne_zero (c : ℝ) (hc : ∀ n : ℤ, (n : ℝ) + c ≠ 0) :
    Summable (fun n : ℤ => 1 / ((n : ℝ) + c) ^ 2) := by
  let k : ℤ := ⌊-c⌋
  have hk_le : (k : ℝ) ≤ -c := Int.floor_le (-c)
  have hk_lt : -c < (k : ℝ) + 1 := Int.lt_floor_add_one (-c)
  have hk_ne : (k : ℝ) + c ≠ 0 := hc k
  have h1 : 0 < -(k + c) := by
    have : (k : ℝ) + c ≤ 0 := by linarith
    exact lt_of_le_of_ne (by linarith) (by intro h; exact hk_ne (by linarith))
  have h2 : 0 < (k : ℝ) + 1 + c := by linarith
  let δ : ℝ := min (-(k + c)) ((k : ℝ) + 1 + c)
  have hδ : 0 < δ := lt_min h1 h2
  have h_lb : ∀ n : ℤ, δ ≤ |(n : ℝ) + c| := by
    intro n
    rcases le_or_gt n k with hn | hn
    · have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
      rw [abs_of_neg (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · have hn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
      rw [abs_of_pos (by linarith)]
      exact (min_le_right _ _).trans (by linarith)
  refine ((summable_inv_one_add_sq_shift c).mul_left (2 * (1 / δ ^ 2 + 1))).of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_)
  have hsq : δ ^ 2 ≤ ((n : ℝ) + c) ^ 2 := by
    rw [← sq_abs ((n : ℝ) + c)]
    exact sq_le_sq' (by linarith [h_lb n]) (h_lb n)
  have hpos : 0 < 1 + |c + (n : ℝ)| := by positivity
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
    inv_eq_one_div, mul_one_div, div_le_div_iff₀ (sq_pos_of_ne_zero (hc n)) (by positivity)]
  have h1 : (1 + |c + (n : ℝ)|) ^ 2 ≤ 2 * (1 + ((n : ℝ) + c) ^ 2) := by
    have h_abs : |c + (n : ℝ)| ^ 2 = ((n : ℝ) + c) ^ 2 := by rw [add_comm, sq_abs]
    nlinarith [sq_nonneg (1 - |c + (n : ℝ)|)]
  have h2 : 1 + ((n : ℝ) + c) ^ 2 ≤ (1 / δ ^ 2 + 1) * ((n : ℝ) + c) ^ 2 := by
    have hinv : 1 ≤ (1 / δ ^ 2) * ((n : ℝ) + c) ^ 2 := by
      rw [one_div_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hδ), one_mul]
      exact hsq
    linarith
  nlinarith [show (0 : ℝ) < 1 / δ ^ 2 + 1 by positivity]

lemma rescaledF_integral_rep (θ Δ x : ℝ) (hΔ : 0 < Δ) (hx : x ≠ 0) :
    rescaledF θ Δ x =
      -(∫ v in Set.Ioo (0 : ℝ) Δ,
        (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v)).im) -
        Real.sin θ * Δ * x / (x ^ 2 + Δ ^ 2) := by
  have h_integrand : ∀ v : ℝ,
      (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v)).im =
        (v * Real.cos θ - x * Real.sin θ) / (x ^ 2 + v ^ 2) := by
    intro v
    have hden : ((x : ℂ) - Complex.I * v) * ((x : ℂ) + Complex.I * v) =
        ((x ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; simp [Complex.I_sq]
    by_cases hxv : (x ^ 2 + v ^ 2 : ℝ) = 0
    · exfalso
      have : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg v]
      exact hx (sq_eq_zero_iff.mp this)
    · have hne : (x : ℂ) - Complex.I * v ≠ 0 := by
        intro h
        rw [h, zero_mul] at hden
        exact hxv (Complex.ofReal_eq_zero.mp hden.symm)
      have hinv : 1 / ((x : ℂ) - Complex.I * v) =
          ((x : ℂ) + Complex.I * v) / ((x ^ 2 + v ^ 2 : ℝ) : ℂ) := by
        rw [div_eq_div_iff hne (Complex.ofReal_ne_zero.mpr hxv), one_mul, mul_comm]
        exact hden.symm
      rw [div_eq_mul_inv, ← one_div, hinv, mul_div_assoc', Complex.div_ofReal_im]
      have hexp : Complex.exp (-Complex.I * θ) =
          ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
        rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_mul_I]
        simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
        ring
      rw [hexp]
      simp only [sub_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_mul, add_zero, sub_zero, Complex.add_re, Complex.add_im]
      ring
  let G : ℝ → ℝ := fun v => (Real.cos θ / 2) * Real.log (x ^ 2 + v ^ 2) - Real.sin θ * Real.arctan (v / x)
  have hG_deriv : ∀ v ∈ Set.uIcc 0 Δ,
      HasDerivAt G ((v * Real.cos θ - x * Real.sin θ) / (x ^ 2 + v ^ 2)) v := by
    intro v _
    have hxv_pos : 0 < x ^ 2 + v ^ 2 := by positivity
    have hd1 : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * v) v :=
      ((hasDerivAt_const v (x ^ 2)).add (hasDerivAt_pow 2 v)).congr_deriv (by ring)
    have hd_log : HasDerivAt (fun t : ℝ => (Real.cos θ / 2) * Real.log (x ^ 2 + t ^ 2))
        ((Real.cos θ / 2) * (2 * v / (x ^ 2 + v ^ 2))) v :=
      (hd1.log hxv_pos.ne').const_mul (Real.cos θ / 2)
    have hd_atan : HasDerivAt (fun t : ℝ => Real.sin θ * Real.arctan (t / x))
        (Real.sin θ * ((1 + (v / x) ^ 2)⁻¹ * (1 / x))) v := by
      have ha := ((hasDerivAt_id v).div_const x).arctan
      simpa [one_div] using ha.const_mul (Real.sin θ)
    refine (hd_log.sub hd_atan).congr_deriv ?_
    field_simp [hx, hxv_pos.ne']
  have hcont : ContinuousOn (fun v : ℝ => (v * Real.cos θ - x * Real.sin θ) / (x ^ 2 + v ^ 2))
      (Set.uIcc 0 Δ) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun v _ => ?_)
    positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv hcont.intervalIntegrable
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hΔ.le]
  simp_rw [h_integrand]
  rw [hftc]
  dsimp only [G]
  simp only [zero_pow two_ne_zero, add_zero, zero_div, Real.arctan_zero, mul_zero, sub_zero]
  have hx2_pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx

  have hlog_sub : Real.log (x ^ 2 + Δ ^ 2) - Real.log (x ^ 2) =
      Real.log (((x / Δ) ^ 2 + 1) / (x / Δ) ^ 2) := by
    rw [← Real.log_div (by positivity) hx2_pos.ne']
    congr 1
    field_simp [hΔ.ne', hx]
  have hatan_eq : Δ / x = 1 / (x / Δ) := by field_simp [hΔ.ne', hx]
  have hfrac_eq : Δ * x / (x ^ 2 + Δ ^ 2) = (x / Δ) / ((x / Δ) ^ 2 + 1) := by
    field_simp [hΔ.ne', hx]
  unfold rescaledF kernelK
  rw [← hlog_sub, ← hatan_eq, ← hfrac_eq]
  ring

lemma rescaledFDeriv_integral_rep (θ Δ x : ℝ) (hΔ : 0 < Δ) (hx : x ≠ 0) :
    rescaledFDeriv θ Δ x =
      (∫ v in Set.Ioo (0 : ℝ) Δ,
        (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v) ^ 2).im) +
        (Δ * Real.sin θ / ((Complex.I * Δ - x) ^ 2)).re := by
  let H : ℝ → ℝ := fun v => -(Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v)).re
  have hH_deriv : ∀ v ∈ Set.uIcc 0 Δ,
      HasDerivAt H ((Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v) ^ 2).im) v := by
    intro v _
    have hne : (x : ℂ) - Complex.I * v ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp at hre
      exact hx hre
    have hd_den : HasDerivAt (fun t : ℝ => (x : ℂ) - Complex.I * t) (-Complex.I) v :=
      ((hasDerivAt_const v (x : ℂ)).sub ((hasDerivAt_id v).ofReal_comp.const_mul Complex.I)).congr_deriv
        (by simp)
    have hd_inv : HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * t))
        (-Complex.exp (-Complex.I * θ) * (-Complex.I) / ((x : ℂ) - Complex.I * v) ^ 2) v := by
      refine ((hasDerivAt_const v (Complex.exp (-Complex.I * θ))).div hd_den hne).congr_deriv ?_
      ring
    have hd_re : HasDerivAt (fun t : ℝ => (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * t)).re)
        ((-Complex.exp (-Complex.I * θ) * (-Complex.I) / ((x : ℂ) - Complex.I * v) ^ 2).re) v :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt v (hd_inv.restrictScalars ℝ)
    refine hd_re.neg.congr_deriv ?_
    have hmul : -(-Complex.exp (-Complex.I * θ) * (-Complex.I) / ((x : ℂ) - Complex.I * v) ^ 2) =
        (-Complex.I) * (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v) ^ 2) := by ring
    rw [← Complex.neg_re, hmul]
    simp [Complex.mul_re]
  have hcont : ContinuousOn (fun v : ℝ => (Complex.exp (-Complex.I * θ) / ((x : ℂ) - Complex.I * v) ^ 2).im)
      (Set.uIcc 0 Δ) := by
    refine Complex.continuous_im.comp_continuousOn ?_
    refine continuousOn_const.div (ContinuousOn.pow (by fun_prop) 2) (fun v _ h => ?_)
    have h0 := sq_eq_zero_iff.mp h
    have hre := congr_arg Complex.re h0
    simp at hre
    exact hx hre
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hH_deriv hcont.intervalIntegrable
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hΔ.le, hftc]
  have hden_Δ : ((x : ℂ) - Complex.I * Δ) * ((x : ℂ) + Complex.I * Δ) = ((x ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; simp [Complex.I_sq]
  have hne_Δ : (x : ℂ) - Complex.I * Δ ≠ 0 := by
    intro h
    have him := congr_arg Complex.im h
    simp at him
    linarith
  have hinv_Δ : 1 / ((x : ℂ) - Complex.I * Δ) = ((x : ℂ) + Complex.I * Δ) / ((x ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
    rw [div_eq_div_iff hne_Δ (Complex.ofReal_ne_zero.mpr (by positivity)), one_mul, mul_comm]
    exact hden_Δ.symm
  have hexp : Complex.exp (-Complex.I * θ) =
      ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hH_Δ : H Δ = -(x * Real.cos θ + Δ * Real.sin θ) / (x ^ 2 + Δ ^ 2) := by
    dsimp only [H]
    rw [div_eq_mul_inv, ← one_div, hinv_Δ, mul_div_assoc', Complex.div_ofReal_re, hexp]
    simp only [sub_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, add_zero, sub_zero, Complex.add_re, Complex.add_im]
    ring
  have hH_0 : H 0 = -(Real.cos θ / x) := by
    dsimp only [H]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    rw [div_eq_mul_inv, hexp]
    have hx_inv : ((x : ℂ))⁻¹ = ((x⁻¹ : ℝ) : ℂ) := (Complex.ofReal_inv x).symm
    rw [hx_inv]
    simp only [sub_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
    ring
  have hbd_re : (Δ * Real.sin θ / ((Complex.I * Δ - x) ^ 2)).re =
      Δ * Real.sin θ * (x ^ 2 - Δ ^ 2) / (x ^ 2 + Δ ^ 2) ^ 2 := by
    have hsq : (Complex.I * Δ - x) ^ 2 = ((x : ℂ) - Complex.I * Δ) ^ 2 := by ring
    rw [hsq, div_eq_mul_inv, ← one_div, ← one_div_pow, hinv_Δ, div_pow, mul_div_assoc',
      ← Complex.ofReal_pow, Complex.div_ofReal_re]
    have hnum : ((x : ℂ) + Complex.I * Δ) ^ 2 =
        ((x ^ 2 - Δ ^ 2 : ℝ) : ℂ) + ((2 * x * Δ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring_nf; simp [Complex.I_sq]
    rw [hnum]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, zero_add]
  rw [hH_Δ, hH_0, hbd_re]
  unfold rescaledFDeriv
  field_simp [hx, (by positivity : (0 : ℝ) < x ^ 2 + Δ ^ 2)]
  ring

lemma partial_fraction_contour {a u w : ℂ} (ha : a ≠ 0) (hu : u ≠ 0) (hw : w ≠ 0)
    (hsum : a = u + w) :
    -1 / (u ^ 2 * w) + 1 / (u * w ^ 2) = -1 / (a * u ^ 2) + 1 / (a * w ^ 2) := by
  field_simp [ha, hu, hw]
  rw [hsum]
  ring

/-- **Lemma 3.2** (Contour integral representation for `M_α(y) - F_{θ,Δ}(y)`). -/
theorem contour_representation (θ Δ α : ℝ) (hθ : |θ| < Real.pi / 2)
    (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ y : ℝ, y ≠ 0 →
      vaalerInterpolant θ Δ α y - rescaledF θ Δ y =
        (Real.sin (Real.pi * (y - α))) ^ 2 *
          ((∫ v in Set.Ioo (0 : ℝ) Δ,
            (Complex.exp (-Complex.I * θ) /
              (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) -
            (Δ * Real.sin θ /
              (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) := by
  intro y hy_ne
  by_cases hlat : ∃ n : ℤ, y = n + α
  · obtain ⟨n, rfl⟩ := hlat
    have hM : vaalerInterpolant θ Δ α (n + α) = rescaledF θ Δ (n + α) := by
      unfold vaalerInterpolant
      simp only [if_pos (⟨n, rfl⟩ : ∃ m : ℤ, (n : ℝ) + α = m + α)]
    have hsin : Real.sin (Real.pi * ((n : ℝ) + α - α)) = 0 := by
      rw [show (n : ℝ) + α - α = (n : ℝ) by ring, mul_comm]
      exact Real.sin_int_mul_pi n
    rw [hM, sub_self, hsin, zero_pow two_ne_zero, zero_mul]
  · have hM : vaalerInterpolant θ Δ α y =
        (Real.sin (Real.pi * (y - α))) ^ 2 / Real.pi ^ 2 *
          ∑' n : ℤ, (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 +
            rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
      unfold vaalerInterpolant
      simp only [if_neg hlat]
    have hsin_ne : Real.sin (Real.pi * (y - α)) ≠ 0 := by
      intro h0
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨n, hn⟩ := h0
      have heq : y - α = n := mul_right_cancel₀ Real.pi_ne_zero (by linarith)
      exact hlat ⟨n, by linarith⟩
    have hΔ_pos : 0 < Δ := by linarith
    have hx_ne : ∀ n : ℤ, (n : ℝ) + α ≠ 0 := by
      intro n h0
      have h2 : (-1 : ℤ) < n := by exact_mod_cast (by linarith [hα.2] : (-1 : ℝ) < (n : ℝ))
      have h3 : n < (0 : ℤ) := by exact_mod_cast (by linarith [hα.1] : (n : ℝ) < 0)
      omega
    have hu_ne : ∀ n : ℤ, y - n - α ≠ 0 := fun n h0 => hlat ⟨n, by linarith⟩
    let d : ℤ → ℝ → ℝ := fun n v =>
      (Complex.exp (-Complex.I * θ) *
        (-1 / (((y : ℂ) - Complex.I * v) * ((y - n - α : ℝ) : ℂ) ^ 2) +
          1 / (((y : ℂ) - Complex.I * v) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2))).im
    let b : ℤ → ℝ := fun n =>
      (Δ * Real.sin θ *
        (-1 / (((y : ℂ) - Complex.I * Δ) * ((y - n - α : ℝ) : ℂ) ^ 2) +
          1 / (((y : ℂ) - Complex.I * Δ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2))).re
    have h_term : ∀ n : ℤ,
        rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α) =
          (∫ v in (0 : ℝ)..Δ, d n v) + b n := by
      intro n
      have hF := rescaledF_integral_rep θ Δ (n + α) hΔ_pos (hx_ne n)
      have hFd := rescaledFDeriv_integral_rep θ Δ (n + α) hΔ_pos (hx_ne n)
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hΔ_pos.le] at hF hFd
      have hF_int : IntervalIntegrable (fun v : ℝ =>
          (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)).im) volume 0 Δ := by
        refine ContinuousOn.intervalIntegrable ?_
        refine Complex.continuous_im.comp_continuousOn ?_
        refine continuousOn_const.div (by fun_prop) (fun v _ h0 => ?_)
        have hre := congr_arg Complex.re h0
        simp at hre
        exact hx_ne n hre
      have hFd_int : IntervalIntegrable (fun v : ℝ =>
          (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2).im) volume 0 Δ := by
        refine ContinuousOn.intervalIntegrable ?_
        refine Complex.continuous_im.comp_continuousOn ?_
        refine continuousOn_const.div (ContinuousOn.pow (by fun_prop) 2) (fun v _ h0 => ?_)
        have h1 := sq_eq_zero_iff.mp h0
        have hre := congr_arg Complex.re h1
        simp at hre
        exact hx_ne n hre
      have h_int_comb :
          -(∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)).im) /
            (y - n - α) ^ 2 +
          (∫ v in (0 : ℝ)..Δ, (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2).im) /
            (y - n - α) =
          ∫ v in (0 : ℝ)..Δ, d n v := by
        have h_add := intervalIntegral.integral_add (hF_int.neg.div_const ((y - n - α) ^ 2))
          (hFd_int.div_const (y - n - α))
        simp only [Pi.neg_apply] at h_add
        rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
          ← h_add]
        congr 1; ext v
        have ha : (y : ℂ) - Complex.I * v ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hy_ne hre
        have hu : ((y - n - α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu_ne n)
        have hw : ((n + α : ℝ) : ℂ) - Complex.I * v ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
        have hpf := partial_fraction_contour ha hu hw (by push_cast; ring)
        have h1 : (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)).im / (y - n - α) ^ 2 =
            (Complex.exp (-Complex.I * θ) * (1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * v)))).im := by
          rw [show Complex.exp (-Complex.I * θ) * (1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * v))) =
            (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v)) / (((y - n - α : ℝ) ^ 2 : ℝ) : ℂ) by
            field_simp [hu, hw]; push_cast; ring, Complex.div_ofReal_im]
        have h2 : (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2).im / (y - n - α) =
            (Complex.exp (-Complex.I * θ) * (1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2))).im := by
          rw [show Complex.exp (-Complex.I * θ) * (1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)) =
            (Complex.exp (-Complex.I * θ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2) / ((y - n - α : ℝ) : ℂ) by
            field_simp [hu, hw]; push_cast; ring, Complex.div_ofReal_im]
        rw [neg_div, h1, h2, ← Complex.neg_im, ← Complex.add_im]
        dsimp only [d]
        congr 1
        calc Complex.exp (-Complex.I * θ) *
              (-(1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * v))) +
                1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2))
            = Complex.exp (-Complex.I * θ) *
                (-1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * v)) +
                  1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)) := by ring_nf
          _ = _ := by rw [hpf]
      have hb_eq :
          -(Real.sin θ * Δ * (n + α) / ((n + α) ^ 2 + Δ ^ 2)) / (y - n - α) ^ 2 +
          (Δ * Real.sin θ / ((Complex.I * Δ - (n + α)) ^ 2)).re / (y - n - α) = b n := by
        have ha : (y : ℂ) - Complex.I * Δ ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hy_ne hre
        have hu : ((y - n - α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu_ne n)
        have hw : ((n + α : ℝ) : ℂ) - Complex.I * Δ ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
        have hpf := partial_fraction_contour ha hu hw (by push_cast; ring)
        have h_re1 : (1 / (((n + α : ℝ) : ℂ) - Complex.I * Δ)).re = (n + α) / ((n + α) ^ 2 + Δ ^ 2) := by
          have hden : (((n + α : ℝ) : ℂ) - Complex.I * Δ) * (((n + α : ℝ) : ℂ) + Complex.I * Δ) =
              (((n + α) ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
            push_cast; ring_nf; simp [Complex.I_sq]
          have hinv : 1 / (((n + α : ℝ) : ℂ) - Complex.I * Δ) =
              (((n + α : ℝ) : ℂ) + Complex.I * Δ) / (((n + α) ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
            rw [div_eq_div_iff hw (Complex.ofReal_ne_zero.mpr (by positivity)), one_mul, mul_comm]
            exact hden.symm
          rw [hinv, Complex.div_ofReal_re]
          simp
        have h1 : Real.sin θ * Δ * (n + α) / ((n + α) ^ 2 + Δ ^ 2) / (y - n - α) ^ 2 =
            ((Δ * Real.sin θ : ℝ) * (1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * Δ)))).re := by
          have hmul : ((Δ * Real.sin θ : ℝ) : ℂ) * (1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * Δ))) =
              ((Δ * Real.sin θ / (y - n - α) ^ 2 : ℝ) : ℂ) * (1 / (((n + α : ℝ) : ℂ) - Complex.I * Δ)) := by
            rw [Complex.ofReal_div, Complex.ofReal_pow, div_mul_div_comm, mul_one, mul_one_div]
          rw [hmul, Complex.re_ofReal_mul, h_re1]; ring
        have h2 : (Δ * Real.sin θ / ((Complex.I * Δ - (n + α)) ^ 2)).re / (y - n - α) =
            ((Δ * Real.sin θ : ℝ) * (1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2))).re := by
          have hmul : ((Δ * Real.sin θ : ℝ) : ℂ) * (1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)) =
              (Δ * Real.sin θ / ((Complex.I * Δ - (n + α)) ^ 2)) / ((y - n - α : ℝ) : ℂ) := by
            have hsq : (Complex.I * Δ - (n + α)) ^ 2 = (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2 := by
              push_cast; ring
            have hsq_ne : (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2 ≠ 0 := pow_ne_zero 2 hw
            rw [hsq]; field_simp [hu, hsq_ne]; push_cast; ring
          rw [hmul, Complex.div_ofReal_re]
        rw [neg_div, h1, h2, ← Complex.neg_re, ← Complex.add_re]
        dsimp only [b]
        congr 1
        rw [show -(((Δ * Real.sin θ : ℝ) : ℂ) * (1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * Δ)))) +
              ((Δ * Real.sin θ : ℝ) : ℂ) * (1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)) =
            ((Δ * Real.sin θ : ℝ) : ℂ) *
              (-1 / (((y - n - α : ℝ) : ℂ) ^ 2 * (((n + α : ℝ) : ℂ) - Complex.I * Δ)) +
                1 / (((y - n - α : ℝ) : ℂ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)) by ring, hpf]
        push_cast; ring
      rw [hF, hFd, ← h_int_comb, ← hb_eq]
      have h_cast : (Complex.I * Δ - (((n : ℝ) + α : ℝ) : ℂ)) ^ 2 = (Complex.I * Δ - ((n : ℂ) + α)) ^ 2 := by
        push_cast; ring
      rw [h_cast]; ring
    have h_summ_u : Summable (fun n : ℤ => 1 / (y - n - α) ^ 2) := by
      have h := summable_inv_add_sq_of_ne_zero (α - y) (fun n h0 => hu_ne n (by linarith))
      refine h.congr fun n => ?_
      ring
    have h_summ_x : Summable (fun n : ℤ => 1 / ((n : ℝ) + α) ^ 2) :=
      summable_inv_add_sq_of_ne_zero α hx_ne
    let M : ℤ → ℝ := fun n => (1 / |y|) * (1 / (y - n - α) ^ 2 + 1 / ((n : ℝ) + α) ^ 2)
    have hM_summ : Summable M := (h_summ_u.add h_summ_x).mul_left (1 / |y|)
    have hd_cont : ∀ n : ℤ, ContinuousOn (d n) (Set.Icc 0 Δ) := by
      intro n
      refine Complex.continuous_im.comp_continuousOn ?_
      refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
      · refine continuousOn_const.div ?_ (fun v _ h0 => ?_)
        · fun_prop
        · have hre := congr_arg Complex.re (mul_eq_zero.mp h0 |>.resolve_right (by
            exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hu_ne n))))
          simp at hre; exact hy_ne hre
      · refine continuousOn_const.div ?_ (fun v _ h0 => ?_)
        · fun_prop
        · rcases mul_eq_zero.mp h0 with h | h
          · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
          · have hre := congr_arg Complex.re (sq_eq_zero_iff.mp h); simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre; exact hx_ne n hre
    have hd_bd : ∀ (n : ℤ) (v : ℝ), v ∈ Set.Icc 0 Δ → ‖d n v‖ ≤ M n := by
      intro n v _
      have ha_norm : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
        have hsq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
            zero_sub, neg_mul]
          nlinarith [sq_nonneg v]
        exact (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp hsq
      have hw_norm : ((n : ℝ) + α) ^ 2 ≤ ‖((n + α : ℝ) : ℂ) - Complex.I * v‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
          zero_sub, neg_mul]
        nlinarith [sq_nonneg v]
      have hexp_norm : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
        rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_ne
      dsimp only [d, M]
      rw [Real.norm_eq_abs]
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, hexp_norm, one_mul]
      refine (norm_add_le _ _).trans ?_
      have ht1 : ‖-1 / (((y : ℂ) - Complex.I * v) * ((y - n - α : ℝ) : ℂ) ^ 2)‖ ≤
          (1 / |y|) * (1 / (y - n - α) ^ 2) := by
        rw [norm_div, norm_neg, norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have hden : |y| * (y - n - α) ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ * (y - n - α) ^ 2 :=
          mul_le_mul_of_nonneg_right ha_norm (sq_nonneg _)
        calc 1 / (‖(y : ℂ) - Complex.I * v‖ * (y - n - α) ^ 2)
            ≤ 1 / (|y| * (y - n - α) ^ 2) :=
              div_le_div_of_nonneg_left zero_le_one (mul_pos hy_abs_pos (sq_pos_of_ne_zero (hu_ne n))) hden
          _ = (1 / |y|) * (1 / (y - n - α) ^ 2) := by simp only [one_div, mul_inv_rev]; ring
      have ht2 : ‖1 / (((y : ℂ) - Complex.I * v) * (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)‖ ≤
          (1 / |y|) * (1 / ((n : ℝ) + α) ^ 2) := by
        rw [norm_div, norm_one, norm_mul, norm_pow]
        have hden : |y| * ((n : ℝ) + α) ^ 2 ≤
            ‖(y : ℂ) - Complex.I * v‖ * ‖((n + α : ℝ) : ℂ) - Complex.I * v‖ ^ 2 :=
          mul_le_mul ha_norm hw_norm (sq_nonneg _) (norm_nonneg _)
        calc 1 / (‖(y : ℂ) - Complex.I * v‖ * ‖((n + α : ℝ) : ℂ) - Complex.I * v‖ ^ 2)
            ≤ 1 / (|y| * ((n : ℝ) + α) ^ 2) :=
              div_le_div_of_nonneg_left zero_le_one (mul_pos hy_abs_pos (sq_pos_of_ne_zero (hx_ne n))) hden
          _ = (1 / |y|) * (1 / ((n : ℝ) + α) ^ 2) := by simp only [one_div, mul_inv_rev]; ring
      linarith
    have h_summ_int : Summable (fun n : ℤ => ∫ v in (0 : ℝ)..Δ, d n v) := by
      refine (hM_summ.mul_right Δ).of_norm_bounded fun n => ?_
      rw [intervalIntegral.integral_of_le hΔ_pos.le]
      calc ‖∫ v in Set.Ioc 0 Δ, d n v‖
          ≤ ∫ v in Set.Ioc 0 Δ, ‖d n v‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ v in Set.Ioc 0 Δ, M n := setIntegral_mono_on
            ((hd_cont n).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self |>.norm)
            (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
            (fun v hv => hd_bd n v (Set.Ioc_subset_Icc_self hv))
        _ = M n * Δ := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hΔ_pos.le, sub_zero, smul_eq_mul, mul_comm]
    have hb_summ : Summable b := by
      refine (hM_summ.mul_left (Δ * |Real.sin θ|)).of_norm_bounded fun n => ?_
      dsimp only [b]
      rw [Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hΔ_pos]
      have ha_norm : |y| ≤ ‖(y : ℂ) - Complex.I * Δ‖ := by
        have hsq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * Δ‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
            zero_sub, neg_mul]
          nlinarith [sq_nonneg Δ]
        exact (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp hsq
      have hw_norm : ((n : ℝ) + α) ^ 2 ≤ ‖((n + α : ℝ) : ℂ) - Complex.I * Δ‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
          zero_sub, neg_mul]
        nlinarith [sq_nonneg Δ]
      have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_ne
      have h_add : ‖-1 / (((y : ℂ) - Complex.I * Δ) * ((y - n - α : ℝ) : ℂ) ^ 2) +
          1 / (((y : ℂ) - Complex.I * Δ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)‖ ≤ M n := by
        refine (norm_add_le _ _).trans ?_
        have ht1 : ‖-1 / (((y : ℂ) - Complex.I * Δ) * ((y - n - α : ℝ) : ℂ) ^ 2)‖ ≤
            (1 / |y|) * (1 / (y - n - α) ^ 2) := by
          rw [norm_div, norm_neg, norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          have hden : |y| * (y - n - α) ^ 2 ≤ ‖(y : ℂ) - Complex.I * Δ‖ * (y - n - α) ^ 2 :=
            mul_le_mul_of_nonneg_right ha_norm (sq_nonneg _)
          calc 1 / (‖(y : ℂ) - Complex.I * Δ‖ * (y - n - α) ^ 2)
              ≤ 1 / (|y| * (y - n - α) ^ 2) :=
                div_le_div_of_nonneg_left zero_le_one (mul_pos hy_abs_pos (sq_pos_of_ne_zero (hu_ne n))) hden
            _ = (1 / |y|) * (1 / (y - n - α) ^ 2) := by simp only [one_div, mul_inv_rev]; ring
        have ht2 : ‖1 / (((y : ℂ) - Complex.I * Δ) * (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)‖ ≤
            (1 / |y|) * (1 / ((n : ℝ) + α) ^ 2) := by
          rw [norm_div, norm_one, norm_mul, norm_pow]
          have hden : |y| * ((n : ℝ) + α) ^ 2 ≤
              ‖(y : ℂ) - Complex.I * Δ‖ * ‖((n + α : ℝ) : ℂ) - Complex.I * Δ‖ ^ 2 :=
            mul_le_mul ha_norm hw_norm (sq_nonneg _) (norm_nonneg _)
          calc 1 / (‖(y : ℂ) - Complex.I * Δ‖ * ‖((n + α : ℝ) : ℂ) - Complex.I * Δ‖ ^ 2)
              ≤ 1 / (|y| * ((n : ℝ) + α) ^ 2) :=
                div_le_div_of_nonneg_left zero_le_one (mul_pos hy_abs_pos (sq_pos_of_ne_zero (hx_ne n))) hden
            _ = (1 / |y|) * (1 / ((n : ℝ) + α) ^ 2) := by simp only [one_div, mul_inv_rev]; ring
        dsimp only [M]; linarith
      exact mul_le_mul_of_nonneg_left h_add (by positivity)
    have h_fubini := intervalIntegral_tsum_of_dominated hΔ_pos.le d M hM_summ hd_cont hd_bd
    have h_tsum_u : (∑' n : ℤ, (1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) =
        ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (y - α)) ^ 2) := by
      have h := (tsum_inv_sub_real_sq (y - α) hsin_ne).2
      have h_eq : (∑' n : ℤ, (1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) =
          ((∑' n : ℤ, 1 / (y - α - n) ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        congr 1; ext n; push_cast; ring
      rw [h_eq, h]
      rw [show (Real.pi : ℂ) * ((y : ℂ) - α) = ((Real.pi * (y - α) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin]
      push_cast; ring
    have h_tsum_w : ∀ v : ℝ, 0 < v →
        (∑' n : ℤ, (1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2) =
          (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 := by
      intro v hv
      have h := (tsum_inv_sub_I_sq (Complex.I * v - α) (by simp [hv])).2
      rw [← h]
      congr 1; ext n
      have : ((n + α : ℝ) : ℂ) - Complex.I * v = -((Complex.I * v - α) - n) := by push_cast; ring
      rw [this, neg_sq]
    have h_d_tsum : ∀ v : ℝ, v ∈ Set.Ioo 0 Δ →
        (∑' n : ℤ, d n v) =
          -(Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im *
            (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) +
          Real.pi ^ 2 * (Complex.exp (-Complex.I * θ) /
            (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im := by
      intro v hv
      have ha : (y : ℂ) - Complex.I * v ≠ 0 := by
        intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hy_ne hre
      have h_summ_c1 : Summable (fun n : ℤ =>
          -Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2)) := by
        have hs : Summable (fun n : ℤ => (1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) := by
          refine Summable.of_norm_bounded h_summ_u (fun n => ?_)
          rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact hs.mul_left _
      have h_summ_c2 : Summable (fun n : ℤ =>
          Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)) := by
        have hs : Summable (fun n : ℤ => (1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2) := by
          refine Summable.of_norm_bounded h_summ_x (fun n => ?_)
          rw [norm_div, norm_one, norm_pow]
          have hw_norm : ((n : ℝ) + α) ^ 2 ≤ ‖((n + α : ℝ) : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
              zero_sub, neg_mul]
            nlinarith [sq_nonneg v]
          exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_ne_zero (hx_ne n)) hw_norm
        exact hs.mul_left _
      have h_eq_c : (fun n : ℤ => d n v) = (fun n : ℤ =>
          (-Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) +
           Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)).im) := by
        ext n; dsimp only [d]; congr 1
        have hu' : ((y - n - α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu_ne n)
        have hw' : ((n + α : ℝ) : ℂ) - Complex.I * v ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hx_ne n hre
        field_simp [ha, hu', hw']
      rw [h_eq_c]
      have h_im_tsum : (∑' n : ℤ,
          (-Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) +
           Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2)).im) =
          (∑' n : ℤ,
            (-Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
              ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) +
             Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
              ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * v) ^ 2))).im :=
        (Complex.im_tsum (h_summ_c1.add h_summ_c2)).symm
      rw [h_im_tsum, h_summ_c1.tsum_add h_summ_c2, tsum_mul_left, tsum_mul_left, h_tsum_u, h_tsum_w v hv.1]
      have h1 : (-Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (y - α)) ^ 2)).im =
          -(Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im *
            (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) := by
        have hr : ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (y - α)) ^ 2) =
            ((Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2 : ℝ) : ℂ) := by
          rw [show (Real.pi : ℂ) * ((y : ℂ) - α) = ((Real.pi * (y - α) : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_sin]
          push_cast; ring
        rw [hr, Complex.im_mul_ofReal, neg_div, Complex.neg_im]
      have h2 : (Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2)).im =
          Real.pi ^ 2 * (Complex.exp (-Complex.I * θ) /
            (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im := by
        have heq : Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v) *
            ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2) =
            (Complex.exp (-Complex.I * θ) /
              (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))) *
              ((Real.pi ^ 2 : ℝ) : ℂ) := by
          rw [div_mul_div_comm, mul_comm ((y : ℂ) - Complex.I * v), ← div_mul_eq_mul_div]
          push_cast; rfl
        rw [heq, Complex.im_mul_ofReal, mul_comm]
      rw [Complex.add_im, h1, h2]
    have hb_tsum : (∑' n : ℤ, b n) =
        -(Real.sin θ * Δ * y / (y ^ 2 + Δ ^ 2)) * (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) -
          Real.pi ^ 2 * (Δ * Real.sin θ /
            (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re := by
      have h_summ_c1 : Summable (fun n : ℤ =>
          -((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
            ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2)) := by
        have hs : Summable (fun n : ℤ => (1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) := by
          refine Summable.of_norm_bounded h_summ_u (fun n => ?_)
          rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact hs.mul_left _
      have h_summ_c2 : Summable (fun n : ℤ =>
          ((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
            ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)) := by
        have hs : Summable (fun n : ℤ => (1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2) := by
          refine Summable.of_norm_bounded h_summ_x (fun n => ?_)
          rw [norm_div, norm_one, norm_pow]
          have hw_norm : ((n : ℝ) + α) ^ 2 ≤ ‖((n + α : ℝ) : ℂ) - Complex.I * Δ‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
              zero_sub, neg_mul]
            nlinarith [sq_nonneg Δ]
          exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_ne_zero (hx_ne n)) hw_norm
        exact hs.mul_left _
      have h_eq_c : b = (fun n : ℤ =>
          (-((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
            ((1 : ℂ) / ((y - n - α : ℝ) : ℂ) ^ 2) +
           ((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
            ((1 : ℂ) / (((n + α : ℝ) : ℂ) - Complex.I * Δ) ^ 2)).re) := by
        ext n; dsimp only [b]; congr 1
        have ha' : (y : ℂ) - Complex.I * Δ ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre
          exact hy_ne hre
        have hu' : ((y - n - α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu_ne n)
        have hw' : ((n + α : ℝ) : ℂ) - Complex.I * Δ ≠ 0 := by
          intro h0; have hre := congr_arg Complex.re h0
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre
          exact hx_ne n hre
        field_simp [ha', hu', hw']; push_cast; ring
      rw [h_eq_c, ← Complex.re_tsum (h_summ_c1.add h_summ_c2), h_summ_c1.tsum_add h_summ_c2,
        tsum_mul_left, tsum_mul_left, h_tsum_u, h_tsum_w Δ hΔ_pos]
      have h1 : (-((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (y - α)) ^ 2)).re =
          -(Real.sin θ * Δ * y / (y ^ 2 + Δ ^ 2)) * (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) := by
        have hr : ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (y - α)) ^ 2) =
            ((Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2 : ℝ) : ℂ) := by
          rw [show (Real.pi : ℂ) * ((y : ℂ) - α) = ((Real.pi * (y - α) : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_sin]
          push_cast; ring
        have h_re_y : (1 / ((y : ℂ) - Complex.I * Δ)).re = y / (y ^ 2 + Δ ^ 2) := by
          have hy_ne_c : (y : ℂ) - Complex.I * Δ ≠ 0 := by
            intro h0; have hre := congr_arg Complex.re h0; simp at hre; exact hy_ne hre
          have hden : ((y : ℂ) - Complex.I * Δ) * ((y : ℂ) + Complex.I * Δ) =
              ((y ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
            push_cast; ring_nf; simp [Complex.I_sq]
          have hinv : 1 / ((y : ℂ) - Complex.I * Δ) = ((y : ℂ) + Complex.I * Δ) / ((y ^ 2 + Δ ^ 2 : ℝ) : ℂ) := by
            rw [div_eq_div_iff hy_ne_c (Complex.ofReal_ne_zero.mpr (by positivity)), one_mul, mul_comm]
            exact hden.symm
          rw [hinv, Complex.div_ofReal_re]
          simp
        rw [hr, Complex.re_mul_ofReal, neg_div, Complex.neg_re,
          show ((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) =
            ((Δ * Real.sin θ : ℝ) : ℂ) * (1 / ((y : ℂ) - Complex.I * Δ)) by ring,
          Complex.re_ofReal_mul, h_re_y]
        ring
      have h2 : (((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2)).re =
          -Real.pi ^ 2 * (Δ * Real.sin θ /
            (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re := by
        have heq : ((Δ * Real.sin θ : ℝ) : ℂ) / ((y : ℂ) - Complex.I * Δ) *
            ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) =
            -(Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))) *
              ((Real.pi ^ 2 : ℝ) : ℂ) := by
          have hneg : (Complex.I * Δ - (y : ℂ)) = -((y : ℂ) - Complex.I * Δ) := by ring
          rw [hneg, mul_neg, div_neg, neg_neg, div_mul_div_comm,
            mul_comm ((y : ℂ) - Complex.I * Δ), ← div_mul_eq_mul_div]
          push_cast; rfl
        rw [heq, Complex.re_mul_ofReal, Complex.neg_re]
        ring
      rw [Complex.add_re, h1, h2]
      ring
    have h_int_split : (∫ v in (0 : ℝ)..Δ, ∑' n : ℤ, d n v) =
        -(∫ v in Set.Ioo (0 : ℝ) Δ, (Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im) *
          (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) +
        Real.pi ^ 2 * (∫ v in Set.Ioo (0 : ℝ) Δ,
          (Complex.exp (-Complex.I * θ) /
            (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im) := by
      rw [intervalIntegral.integral_of_le hΔ_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have h_congr : Set.EqOn (fun v => ∑' n : ℤ, d n v)
          (fun v => -(Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im *
            (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2) +
            Real.pi ^ 2 * (Complex.exp (-Complex.I * θ) /
              (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im)
          (Set.Ioo 0 Δ) := fun v hv => h_d_tsum v hv
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h_congr]
      have h_i1 : IntegrableOn (fun v : ℝ =>
          -(Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im *
            (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2)) (Set.Ioo 0 Δ) := by
        have hc1 : Continuous (fun v : ℝ =>
            -(Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im *
              (Real.pi ^ 2 / Real.sin (Real.pi * (y - α)) ^ 2)) := by
          refine (Complex.continuous_im.comp (continuous_const.div
            (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)) (fun v h0 => ?_))).neg.mul continuous_const
          have hre := congr_arg Complex.re h0; simp at hre; exact hy_ne hre
        exact hc1.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
      have h_i2 : IntegrableOn (fun v : ℝ =>
          Real.pi ^ 2 * (Complex.exp (-Complex.I * θ) /
            (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im)
          (Set.Ioo 0 Δ) := by
        have hc2 : Continuous (fun v : ℝ =>
            Real.pi ^ 2 * (Complex.exp (-Complex.I * θ) /
              (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im) := by
          refine continuous_const.mul (Complex.continuous_im.comp (continuous_const.div ?_ (fun v h0 => ?_)))
          · exact ((Complex.continuous_sin.comp (continuous_const.mul
              ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const))).pow 2).mul
              (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal))
          · rcases mul_eq_zero.mp h0 with hsin | hden
            · have hsin0 := sq_eq_zero_iff.mp hsin
              rw [Complex.sin_eq_zero_iff] at hsin0
              obtain ⟨k, hk⟩ := hsin0
              have hre := congr_arg Complex.re hk
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
                Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_re, zero_sub,
                Complex.intCast_re] at hre
              have h_eq : -α = (k : ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by linarith)
              have : (-1 : ℤ) < k := by exact_mod_cast (by linarith [hα.2] : (-1 : ℝ) < k)
              have : k < (0 : ℤ) := by exact_mod_cast (by linarith [hα.1] : (k : ℝ) < 0)
              omega
            · have hre := congr_arg Complex.re hden; simp at hre; exact hy_ne hre
        exact hc2.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
      rw [MeasureTheory.integral_add h_i1 h_i2, MeasureTheory.integral_mul_const,
        MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    rw [hM]
    rw [tsum_congr h_term]
    rw [h_summ_int.tsum_add hb_summ, ← h_fubini, h_int_split, hb_tsum]
    have hFy := rescaledF_integral_rep θ Δ y hΔ_pos hy_ne
    rw [hFy]
    generalize (∫ v in Set.Ioo (0 : ℝ) Δ, (Complex.exp (-Complex.I * θ) / ((y : ℂ) - Complex.I * v)).im) = I1
    generalize (∫ v in Set.Ioo (0 : ℝ) Δ, (Complex.exp (-Complex.I * θ) /
      (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * ((y : ℂ) - Complex.I * v))).im) = I2
    generalize (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re = B
    field_simp [Real.pi_ne_zero, hsin_ne]
    ring

lemma cTheta_re_pos {θ v : ℝ} (hθ : |θ| < Real.pi / 2) (hv : 0 ≤ v) :
    0 < (cTheta θ v).re := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hcos_c : Complex.cos (θ + Complex.I * Real.pi * v) =
      ((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) -
        ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add]
    have h1 : Complex.cos (Complex.I * Real.pi * v) = Real.cosh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.cos_mul_I]
      rw [← Complex.ofReal_cosh]
    have h2 : Complex.sin (Complex.I * Real.pi * v) = Complex.I * Real.sinh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.sin_mul_I]
      rw [← Complex.ofReal_sinh]; ring
    rw [h1, h2]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have hD_pos : 0 < Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by positivity
  have h_re_eq : (cTheta θ v).re =
      Real.cos θ * (Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 +
        Real.sin θ ^ 2 * (2 * Real.sinh (Real.pi * v) * Real.cosh (Real.pi * v) -
          Real.sinh (Real.pi * v) ^ 2)) / (Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2) ^ 2 := by
    dsimp only [cTheta]
    have hne : Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := cos_ne_zero_of_abs_lt hθ
    have hconj : Complex.cos (θ + Complex.I * Real.pi * v) *
        (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
          ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) =
        ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
      rw [hcos_c]
      have hch := Real.cosh_sq (Real.pi * v)
      have hcs := Real.cos_sq_add_sin_sq θ
      calc (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) -
              ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) *
            (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
              ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I)
          = (((Real.cos θ * Real.cosh (Real.pi * v)) ^ 2 +
              (Real.sin θ * Real.sinh (Real.pi * v)) ^ 2 : ℝ) : ℂ) := by
            push_cast; ring_nf; rw [Complex.I_sq]; ring
        _ = ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
            congr 1; nlinarith
    have hinv : 1 / Complex.cos (θ + Complex.I * Real.pi * v) =
        (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
          ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) /
        ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
      rw [div_eq_div_iff hne (Complex.ofReal_ne_zero.mpr hD_pos.ne'), one_mul, ← hconj]; ring
    have hexp : Complex.exp (-Complex.I * θ) =
        ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I]
      simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    rw [div_eq_mul_inv, ← one_div, ← one_div_pow, hinv, div_pow, mul_div_assoc',
      ← Complex.ofReal_pow, Complex.div_ofReal_re, hexp]
    have h_alg_gen : ∀ a b c d : ℝ,
        ((a : ℂ) - (b : ℂ) * Complex.I) *
          (((a * c : ℝ) : ℂ) + ((b * d : ℝ) : ℂ) * Complex.I) ^ 2 =
          ((a * (a ^ 2 * c ^ 2 + b ^ 2 * (2 * d * c - d ^ 2)) : ℝ) : ℂ) +
          ((b * (-a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + 2 * a ^ 2 * d * c) : ℝ) : ℂ) * Complex.I := by
      intro a b c d
      apply Complex.ext <;> simp [sq] <;> ring
    rw [h_alg_gen (Real.cos θ) (Real.sin θ) (Real.cosh (Real.pi * v)) (Real.sinh (Real.pi * v))]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [h_re_eq]
  have hsh_nonneg : 0 ≤ Real.sinh (Real.pi * v) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hch_ge : Real.sinh (Real.pi * v) < 2 * Real.cosh (Real.pi * v) := by
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos (Real.pi * v), Real.exp_pos (-(Real.pi * v))]
  have h_pos_num : 0 < Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 +
      Real.sin θ ^ 2 * (2 * Real.sinh (Real.pi * v) * Real.cosh (Real.pi * v) -
        Real.sinh (Real.pi * v) ^ 2) := by
    have h1 : 0 < Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 := by
      have : 0 < Real.cosh (Real.pi * v) := Real.cosh_pos _
      positivity
    have h2 : 0 ≤ Real.sin θ ^ 2 * (2 * Real.sinh (Real.pi * v) * Real.cosh (Real.pi * v) -
        Real.sinh (Real.pi * v) ^ 2) := by
      refine mul_nonneg (sq_nonneg _) ?_
      have : 2 * Real.sinh (Real.pi * v) * Real.cosh (Real.pi * v) - Real.sinh (Real.pi * v) ^ 2 =
          Real.sinh (Real.pi * v) * (2 * Real.cosh (Real.pi * v) - Real.sinh (Real.pi * v)) := by ring
      rw [this]
      exact mul_nonneg hsh_nonneg (by linarith)
    linarith
  exact div_pos (mul_pos hcos_pos h_pos_num) (sq_pos_of_pos hD_pos)

lemma cTheta_im_eq {θ v : ℝ} (hθ : |θ| < Real.pi / 2) :
    (cTheta θ v).im =
      Real.sin θ * (-Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 +
        Real.sin θ ^ 2 * Real.sinh (Real.pi * v) ^ 2 +
        2 * Real.cos θ ^ 2 * Real.sinh (Real.pi * v) * Real.cosh (Real.pi * v)) /
      (Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2) ^ 2 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hcos_c : Complex.cos (θ + Complex.I * Real.pi * v) =
      ((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) -
        ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add]
    have h1 : Complex.cos (Complex.I * Real.pi * v) = Real.cosh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.cos_mul_I]
      rw [← Complex.ofReal_cosh]
    have h2 : Complex.sin (Complex.I * Real.pi * v) = Complex.I * Real.sinh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.sin_mul_I]
      rw [← Complex.ofReal_sinh]; ring
    rw [h1, h2]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have hD_pos : 0 < Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by positivity
  have hne : Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := cos_ne_zero_of_abs_lt hθ
  have hconj : Complex.cos (θ + Complex.I * Real.pi * v) *
      (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
        ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) =
      ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
    rw [hcos_c]
    have hch := Real.cosh_sq (Real.pi * v)
    have hcs := Real.cos_sq_add_sin_sq θ
    calc (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) -
            ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) *
          (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
            ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I)
        = (((Real.cos θ * Real.cosh (Real.pi * v)) ^ 2 +
            (Real.sin θ * Real.sinh (Real.pi * v)) ^ 2 : ℝ) : ℂ) := by
          push_cast; ring_nf; rw [Complex.I_sq]; ring
      _ = ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
          congr 1; nlinarith
  have hinv : 1 / Complex.cos (θ + Complex.I * Real.pi * v) =
      (((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
        ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I) /
      ((Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by
    rw [div_eq_div_iff hne (Complex.ofReal_ne_zero.mpr hD_pos.ne'), one_mul, ← hconj]; ring
  have hexp : Complex.exp (-Complex.I * θ) =
      ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  dsimp only [cTheta]
  rw [div_eq_mul_inv, ← one_div, ← one_div_pow, hinv, div_pow, mul_div_assoc',
    ← Complex.ofReal_pow, Complex.div_ofReal_im, hexp]
  have h_alg_gen : ∀ a b c d : ℝ,
      ((a : ℂ) - (b : ℂ) * Complex.I) *
        (((a * c : ℝ) : ℂ) + ((b * d : ℝ) : ℂ) * Complex.I) ^ 2 =
        ((a * (a ^ 2 * c ^ 2 + b ^ 2 * (2 * d * c - d ^ 2)) : ℝ) : ℂ) +
        ((b * (-a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + 2 * a ^ 2 * d * c) : ℝ) : ℂ) * Complex.I := by
    intro a b c d
    apply Complex.ext <;> simp [sq] <;> ring
  rw [h_alg_gen (Real.cos θ) (Real.sin θ) (Real.cosh (Real.pi * v)) (Real.sinh (Real.pi * v))]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one, zero_mul, add_zero, zero_add]

lemma limitingJ_pos_of_neg {θ y : ℝ} (hθ : 0 ≤ θ) (hθ_lt : θ < Real.pi / 2)
    (hy : y < 0) : 0 < limitingJ y θ := by
  have hy_sq : 0 < y ^ 2 := sq_pos_of_neg hy
  have hθ_abs : |θ| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [Real.pi_pos], hθ_lt⟩
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ_abs)
  have hc_int := cTheta_integrableOn hθ_abs
  have h_integrand : ∀ v : ℝ,
      (Complex.exp (-Complex.I * θ) /
        (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im =
        v * (cTheta θ v).re / (y ^ 2 + v ^ 2) + y * (cTheta θ v).im / (y ^ 2 + v ^ 2) := by
    intro v
    have hden : ((y : ℂ) - Complex.I * v) * ((y : ℂ) + Complex.I * v) = ((y ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; simp [Complex.I_sq]
    have hne : (y : ℂ) - Complex.I * v ≠ 0 := by
      intro h0; have hre := congr_arg Complex.re h0; simp at hre; linarith
    have hinv : 1 / ((y : ℂ) - Complex.I * v) = ((y : ℂ) + Complex.I * v) / ((y ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      rw [div_eq_div_iff hne (Complex.ofReal_ne_zero.mpr (by positivity)), one_mul, mul_comm]
      exact hden.symm
    have heq : Complex.exp (-Complex.I * θ) /
        (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v)) =
        cTheta θ v * (1 / ((y : ℂ) - Complex.I * v)) := by
      dsimp only [cTheta]
      field_simp [pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ_abs), hne]
    rw [heq, hinv, mul_div_assoc', Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
      Complex.add_im, zero_add]
    ring
  have h_int_re : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
    have h_meas : AEStronglyMeasurable (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2))
        (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity))
      refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
      exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ_abs)
    refine (hc_int.norm.const_mul (1 / |y|)).mono' h_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have h2 : |v| / (y ^ 2 + v ^ 2) ≤ 1 / (2 * |y|) := by
      have hy_pos : 0 < |y| := abs_pos.mpr hy.ne
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (|v| - |y|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs v, sq_abs y]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2)]
    calc |v| * |(cTheta θ v).re| / (y ^ 2 + v ^ 2)
        = (|v| / (y ^ 2 + v ^ 2)) * |(cTheta θ v).re| := by ring
      _ ≤ (1 / |y|) * ‖cTheta θ v‖ :=
          mul_le_mul (h2.trans (div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr hy.ne)
            (by linarith [abs_pos.mpr hy.ne]))) (Complex.abs_re_le_norm _) (abs_nonneg _) (by positivity)
  have h_int_im : IntegrableOn (fun v : ℝ => y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
    have h_meas : AEStronglyMeasurable (fun v : ℝ => y * (cTheta θ v).im / (y ^ 2 + v ^ 2))
        (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_const.mul (Complex.continuous_im.comp ?_)).div (by fun_prop) (fun v => by positivity))
      refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
      exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ_abs)
    refine (hc_int.norm.const_mul (1 / |y|)).mono' h_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2)]
    have h1 : |y| / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
      rw [div_le_div_iff₀ (by positivity) (abs_pos.mpr hy.ne)]
      nlinarith [sq_abs y, sq_nonneg v]
    calc |y| * |(cTheta θ v).im| / (y ^ 2 + v ^ 2)
        = (|y| / (y ^ 2 + v ^ 2)) * |(cTheta θ v).im| := by ring
      _ ≤ (1 / |y|) * ‖cTheta θ v‖ := mul_le_mul h1 (Complex.abs_im_le_norm _) (abs_nonneg _) (by positivity)
  have hJ_split : limitingJ y θ =
      (∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
    unfold limitingJ
    simp_rw [h_integrand]
    exact MeasureTheory.integral_add h_int_re h_int_im
  have h_pos_first : 0 < ∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2) := by
    let g : ℝ → ℝ := fun v => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)
    have hg_cont : Continuous g := by
      refine ((continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity))
      refine continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => ?_)
      exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ_abs)
    obtain ⟨v_min, hv_min, hv_isMin⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMinOn
      ⟨(1 : ℝ), by norm_num⟩ hg_cont.continuousOn
    have hg_min_pos : 0 < g v_min := by
      have hv1 : 1 ≤ v_min := hv_min.1
      have hv_pos : 0 < v_min := by linarith
      have hre_pos := cTheta_re_pos hθ_abs (by linarith)
      dsimp only [g]
      positivity
    have h_Ioc_le : ∫ v in Set.Ioc (1 : ℝ) 2, g v ≤ ∫ v in Set.Ioi (0 : ℝ), g v := by
      refine MeasureTheory.setIntegral_mono_set h_int_re ?_ (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi zero_le_one)).eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hre_pos := cTheta_re_pos hθ_abs hv.le
      dsimp only [g]; exact div_nonneg (mul_nonneg hv.le hre_pos.le) (by positivity)
    have h_min_le : g v_min ≤ ∫ v in Set.Ioc (1 : ℝ) 2, g v := by
      have h_const : ∫ _ in Set.Ioc (1 : ℝ) 2, g v_min = g v_min := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
        norm_num
      rw [← h_const]
      have h_c_int : IntegrableOn (fun _ : ℝ => g v_min) (Set.Ioc 1 2) :=
        (continuousOn_const : ContinuousOn (fun _ : ℝ => g v_min) (Set.Icc 1 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have h_g_int : IntegrableOn g (Set.Ioc 1 2) :=
        (hg_cont.continuousOn : ContinuousOn g (Set.Icc 1 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      refine MeasureTheory.setIntegral_mono_on h_c_int h_g_int measurableSet_Ioc
        fun v hv => hv_isMin (Set.Ioc_subset_Icc_self hv)
    linarith
  have h_nonneg_second : 0 ≤ ∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2) := by
    by_cases hθ0 : θ = 0
    · have him0 : ∀ v : ℝ, (cTheta 0 v).im = 0 := fun v => by
        rw [cTheta_im_eq (by simp [Real.pi_pos])]
        simp
      have : (fun v : ℝ => y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) = 0 := by
        ext v; rw [hθ0, him0]; simp
      simp [this]
    · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
      have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
      let t : ℝ → ℝ := fun v => Real.sinh (Real.pi * v) / Real.cosh (Real.pi * v)
      let h : ℝ → ℝ := fun v => -Real.cos θ ^ 2 + Real.sin θ ^ 2 * (t v) ^ 2 + 2 * Real.cos θ ^ 2 * t v
      have ht_strict : StrictMono t := by
        intro a b hab
        have ha_eq : t a = 1 - 2 / (Real.exp (2 * Real.pi * a) + 1) := by
          dsimp only [t]
          rw [Real.sinh_eq, Real.cosh_eq]
          have he : Real.exp (2 * Real.pi * a) = Real.exp (Real.pi * a) * Real.exp (Real.pi * a) := by
            rw [← Real.exp_add]; ring_nf
          rw [he, Real.exp_neg]
          field_simp [(Real.exp_pos (Real.pi * a)).ne', (by positivity : Real.exp (Real.pi * a) + (Real.exp (Real.pi * a))⁻¹ ≠ 0), (by positivity : Real.exp (Real.pi * a) * Real.exp (Real.pi * a) + 1 ≠ 0)]
          ring
        have hb_eq : t b = 1 - 2 / (Real.exp (2 * Real.pi * b) + 1) := by
          dsimp only [t]
          rw [Real.sinh_eq, Real.cosh_eq]
          have he : Real.exp (2 * Real.pi * b) = Real.exp (Real.pi * b) * Real.exp (Real.pi * b) := by
            rw [← Real.exp_add]; ring_nf
          rw [he, Real.exp_neg]
          field_simp [(Real.exp_pos (Real.pi * b)).ne', (by positivity : Real.exp (Real.pi * b) + (Real.exp (Real.pi * b))⁻¹ ≠ 0), (by positivity : Real.exp (Real.pi * b) * Real.exp (Real.pi * b) + 1 ≠ 0)]
          ring
        rw [ha_eq, hb_eq]
        have hexp : Real.exp (2 * Real.pi * a) < Real.exp (2 * Real.pi * b) := by
          gcongr
        have hden : 2 / (Real.exp (2 * Real.pi * b) + 1) < 2 / (Real.exp (2 * Real.pi * a) + 1) := by
          gcongr
        linarith
      have ht_nonneg : ∀ v ≥ 0, 0 ≤ t v := fun v hv =>
        div_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)) (Real.cosh_pos _).le
      have ht_lt_one : ∀ v : ℝ, t v < 1 := fun v => by
        dsimp only [t]
        rw [div_lt_one (Real.cosh_pos _), Real.sinh_eq, Real.cosh_eq]
        linarith [Real.exp_pos (-(Real.pi * v))]
      have hh_strict : StrictMonoOn h (Set.Ici 0) := by
        intro a ha b hb hab
        have hta : 0 ≤ t a := ht_nonneg a ha
        have htb : t a < t b := ht_strict hab
        dsimp only [h]
        have hsq : t a ^ 2 ≤ t b ^ 2 := sq_le_sq' (by linarith) htb.le
        nlinarith [sq_pos_of_pos hcos_pos, sq_nonneg (Real.sin θ)]
      have hh_cont : Continuous h := by
        dsimp only [h, t]
        have ht_cont : Continuous (fun v : ℝ => Real.sinh (Real.pi * v) / Real.cosh (Real.pi * v)) :=
          (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
            (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) (fun v => (Real.cosh_pos _).ne')
        exact (continuous_const.add (continuous_const.mul (ht_cont.pow 2))).add (continuous_const.mul ht_cont)
      have hh_0 : h 0 < 0 := by
        dsimp only [h, t]
        simp [Real.sinh_zero]
        exact sq_pos_of_pos hcos_pos
      have hh_lim : ∃ V > 0, 0 < h V := by
        have h_lim_t : Tendsto t atTop (nhds 1) := by
          have heq : t = fun v => 1 - 2 / (Real.exp (2 * Real.pi * v) + 1) := by
            ext v; dsimp only [t]; rw [Real.sinh_eq, Real.cosh_eq]
            have he : Real.exp (2 * Real.pi * v) = Real.exp (Real.pi * v) * Real.exp (Real.pi * v) := by
              rw [← Real.exp_add]; ring_nf
            rw [he, Real.exp_neg]
            field_simp [(Real.exp_pos (Real.pi * v)).ne', (by positivity : Real.exp (Real.pi * v) + (Real.exp (Real.pi * v))⁻¹ ≠ 0), (by positivity : Real.exp (Real.pi * v) * Real.exp (Real.pi * v) + 1 ≠ 0)]
            ring
          rw [heq]
          have h_exp : Tendsto (fun v : ℝ => Real.exp (2 * Real.pi * v)) atTop atTop :=
            Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
          have h_div : Tendsto (fun v : ℝ => 2 / (Real.exp (2 * Real.pi * v) + 1)) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop (h_exp.atTop_add tendsto_const_nhds)
          simpa using tendsto_const_nhds.sub h_div
        have h_lim_h : Tendsto h atTop (nhds 1) := by
          have h1 : Tendsto (fun v => -Real.cos θ ^ 2 + Real.sin θ ^ 2 * (t v) ^ 2 + 2 * Real.cos θ ^ 2 * t v)
              atTop (nhds (-Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1 ^ 2 + 2 * Real.cos θ ^ 2 * 1)) := by
            exact ((tendsto_const_nhds.add ((h_lim_t.pow 2).const_mul _)).add (h_lim_t.const_mul _))
          have hcs := Real.cos_sq_add_sin_sq θ
          change Tendsto h atTop (nhds 1)
          rw [show (1 : ℝ) = -Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1 ^ 2 + 2 * Real.cos θ ^ 2 * 1 by linarith]
          exact h1
        obtain ⟨V, hV⟩ := (h_lim_h.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))).exists_forall_of_atTop
        refine ⟨max V 1, by positivity, hV (max V 1) (le_max_left _ _)⟩
      obtain ⟨V, hV_pos, hV_gt⟩ := hh_lim
      obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := intermediate_value_Icc hV_pos.le hh_cont.continuousOn ⟨hh_0.le, hV_gt.le⟩
      have h_im_h : ∀ v : ℝ, (cTheta θ v).im =
          Real.sin θ * Real.cosh (Real.pi * v) ^ 2 * h v / (Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2) ^ 2 := by
        intro v
        rw [cTheta_im_eq hθ_abs]
        dsimp only [h, t]
        have hch_ne : Real.cosh (Real.pi * v) ≠ 0 := (Real.cosh_pos _).ne'
        field_simp [hch_ne]
      have h_int_sub : IntegrableOn (fun v : ℝ => (cTheta θ v).im / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
        have h_eq : (fun v : ℝ => (cTheta θ v).im / (y ^ 2 + v ^ 2)) =
            fun v => (1 / y) * (y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
          ext v; field_simp [hy.ne]
        rw [h_eq]; exact h_int_im.const_mul (1 / y)
      have h_int_const : IntegrableOn (fun v : ℝ => (cTheta θ v).im / (y ^ 2 + v₀ ^ 2)) (Set.Ioi 0) :=
        (Complex.imCLM.integrable_comp hc_int).div_const (y ^ 2 + v₀ ^ 2)
      have h_zero_const : ∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im / (y ^ 2 + v₀ ^ 2) = 0 := by
        rw [MeasureTheory.integral_div, cTheta_im_integral_zero hθ_abs, zero_div]
      have h_le_zero : ∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im / (y ^ 2 + v ^ 2) ≤ 0 := by
        rw [← sub_zero (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im / (y ^ 2 + v ^ 2))]
        nth_rw 2 [← h_zero_const]
        rw [← MeasureTheory.integral_sub h_int_sub h_int_const]
        refine MeasureTheory.setIntegral_nonpos measurableSet_Ioi fun v hv => ?_
        have hv_nonneg : 0 ≤ v := hv.le
        rw [h_im_h v]
        rcases le_total v v₀ with hle | hge
        · have hh_le : h v ≤ 0 := by
            rcases eq_or_lt_of_le hle with rfl | hlt
            · exact hv₀_eq.le
            · rw [← hv₀_eq]; exact (hh_strict hv_nonneg hv₀_mem.1 hlt).le
          have hden_le : 1 / (y ^ 2 + v₀ ^ 2) ≤ 1 / (y ^ 2 + v ^ 2) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity)
              (by have := sq_le_sq' (by linarith) hle; linarith)
          have h_im_nonpos : Real.sin θ * Real.cosh (Real.pi * v) ^ 2 * h v /
              (Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2) ^ 2 ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsin_pos.le (sq_nonneg _)) hh_le)
              (sq_nonneg _)
          calc _ / (y ^ 2 + v ^ 2) - _ / (y ^ 2 + v₀ ^ 2)
              = _ * (1 / (y ^ 2 + v ^ 2) - 1 / (y ^ 2 + v₀ ^ 2)) := by ring
            _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h_im_nonpos (by linarith)
        · have hh_ge : 0 ≤ h v := by
            rcases eq_or_lt_of_le hge with rfl | hlt
            · exact hv₀_eq.ge
            · rw [← hv₀_eq]; exact (hh_strict hv₀_mem.1 hv_nonneg hlt).le
          have hden_ge : 1 / (y ^ 2 + v ^ 2) ≤ 1 / (y ^ 2 + v₀ ^ 2) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity)
              (by have := sq_le_sq' (by linarith [hv₀_mem.1]) hge; linarith)
          have h_im_nonneg : 0 ≤ Real.sin θ * Real.cosh (Real.pi * v) ^ 2 * h v /
              (Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2) ^ 2 := by
            positivity
          calc _ / (y ^ 2 + v ^ 2) - _ / (y ^ 2 + v₀ ^ 2)
              = _ * (1 / (y ^ 2 + v ^ 2) - 1 / (y ^ 2 + v₀ ^ 2)) := by ring
            _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h_im_nonneg (by linarith)
      have h_mul_eq : (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) =
          y * (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
        rw [← MeasureTheory.integral_const_mul]
        congr 1; ext v; ring
      rw [h_mul_eq]
      exact mul_nonneg_of_nonpos_of_nonpos hy.le h_le_zero
  linarith


end PolarEvaluation
