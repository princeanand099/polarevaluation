import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults

/-!
# Explicit Formulae and Fourier Analysis of the Kernel (Section 2)

Formalizes Lemma 2.1 (`horizontal_zero_sum`), Lemma 2.2 (`guinand_weil_bandlimited`),
and Lemma 2.3 (`kernelK_fourier` and `majorant_fourier_decay`).
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

/-- **Lemma 2.1** (Horizontal zero-sum representation). -/
theorem horizontal_zero_sum (D : LFunctionData) :
    ∃ C₀ : ℝ, C₀ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (θ : ℝ), |θ| < Real.pi / 2 →
        ∀ (t : ℝ), D.nonvanishing q χ t → (q = 1 → |t| ≥ 10) →
          Summable (fun n : ℕ => kernelK θ (t - D.zeros q χ n)) ∧
          |polarLogL D q χ t θ -
            ((Real.cos θ / 2) * Real.log (analyticConductor q t) +
              ∑' n : ℕ, kernelK θ (t - D.zeros q χ n))| ≤ C₀ :=
  horizontal_zero_sum_external D

/-- **Lemma 2.2** (Guinand–Weil Explicit Formula for bandlimited test functions). -/
theorem guinand_weil_bandlimited (D : LFunctionData) :
    ∃ C₁ : ℝ, C₁ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (h : ℂ → ℂ) (Δ M_sup : ℝ), Δ ≥ 1 → M_sup ≥ 0 →
          HasExponentialType h (2 * Real.pi * Δ) →
          (∀ x : ℝ, ‖h x‖ ≤ M_sup / (1 + x ^ 2)) →
          (∀ x : ℝ, (h x).im = 0) →
          ∀ (t : ℝ), (q = 1 → |t| ≥ 10) →
            Summable (fun n : ℕ => (h (t - D.zeros q χ n)).re) ∧
            |∑' n : ℕ, (h (t - D.zeros q χ n)).re -
              ((Real.log (analyticConductor q t) / (2 * Real.pi)) * (∫ x : ℝ, (h x).re) -
                primePowerSum q χ (fourierHat (fun x : ℝ => h x)) (Real.exp (2 * Real.pi * Δ)) t)| ≤
              C₁ * (M_sup + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * M_sup else 0)) :=
  guinand_weil_external D

lemma kernelK_integrable_zero : Integrable (fun x : ℝ => kernelK 0 x) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => kernelK 0 x) volume := by
    unfold kernelK
    fun_prop
  have h_Ioi : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Ioi (1 : ℝ)) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine hpow.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx_pos : 0 < x := by linarith
    have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    unfold kernelK
    simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
    have hlog_nonneg : 0 ≤ Real.log ((x ^ 2 + 1) / x ^ 2) := by
      apply Real.log_nonneg
      rw [one_le_div hx2_pos]
      linarith
    have hlog_le : Real.log ((x ^ 2 + 1) / x ^ 2) ≤ 1 / x ^ 2 := by
      calc Real.log ((x ^ 2 + 1) / x ^ 2)
          ≤ (x ^ 2 + 1) / x ^ 2 - 1 := Real.log_le_sub_one_of_pos (div_pos (by positivity) hx2_pos)
        _ = 1 / x ^ 2 := by field_simp; ring
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hlog_nonneg]
    have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
    rw [hrpow]
    linarith
  have h_Iio : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Iio (-1 : ℝ)) := by
    have h_even : ∀ x : ℝ, kernelK 0 (-x) = kernelK 0 x := by
      intro x; unfold kernelK; simp [Real.cos_zero, Real.sin_zero]
    have hcomp : IntegrableOn (fun x : ℝ => kernelK 0 (-x)) (Set.Ioi (1 : ℝ)) := by
      simpa [h_even] using h_Ioi
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by
      ext x; simp
    simpa [hpre] using hcomp.comp_neg
  have h_Icc : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Icc (-1 : ℝ) 1) := by
    have h_log_abs : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (-1 : ℝ) 1) := by
      have h01 : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (0 : ℝ) 1) := by
        have hrpow_ioc : IntegrableOn (fun x : ℝ => 2 * x ^ (-1 / 2 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
            (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2))).const_mul 2
        have hrpow : IntegrableOn (fun x : ℝ => 2 * x ^ (-1 / 2 : ℝ)) (Set.Icc (0 : ℝ) 1) :=
          hrpow_ioc.congr_set_ae Ioc_ae_eq_Icc.symm
        have hmeas_log : AEStronglyMeasurable (fun x : ℝ => Real.log |x|) volume :=
          (Real.measurable_log.comp measurable_abs).aestronglyMeasurable
        refine hrpow.mono' hmeas_log.restrict ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        by_cases hx0 : x = 0
        · subst hx0; simp
        · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          have h_inv : 0 < x ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
          have hlog_neg : Real.log x ≤ 0 := Real.log_nonpos hx_pos.le hx.2
          have hbound : -Real.log x ≤ 2 * x ^ (-1 / 2 : ℝ) := by
            have h1 : Real.log (x ^ (-1 / 2 : ℝ)) ≤ x ^ (-1 / 2 : ℝ) - 1 :=
              Real.log_le_sub_one_of_pos h_inv
            rw [Real.log_rpow hx_pos] at h1
            linarith
          rw [Real.norm_eq_abs, abs_of_pos hx_pos, abs_of_nonpos hlog_neg]
          exact hbound
      have h_neg : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (-1 : ℝ) 0) := by
        have hpre : (fun x : ℝ => -x) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (-1 : ℝ) 0 := by
          ext x; simp
        simpa [abs_neg, hpre] using h01.comp_neg
      simpa [Set.Icc_union_Icc_eq_Icc (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)] using
        h_neg.union h01
    have h_log_sq : IntegrableOn (fun x : ℝ => Real.log (x ^ 2 + 1)) (Set.Icc (-1 : ℝ) 1) :=
      (Continuous.continuousOn (Continuous.log (by fun_prop) (fun x => by positivity))).integrableOn_Icc
    have h_comb : IntegrableOn (fun x : ℝ => -(1 / 2 : ℝ) * (Real.log (x ^ 2 + 1) - 2 * Real.log |x|))
        (Set.Icc (-1 : ℝ) 1) :=
      (h_log_sq.sub (h_log_abs.const_mul 2)).const_mul (-(1 / 2 : ℝ))
    refine h_comb.congr_fun_ae ?_
    have hne : ∀ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)), x ≠ 0 :=
      ae_restrict_of_ae (ae_iff.mpr (by simp))
    filter_upwards [hne] with x hx
    unfold kernelK
    simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
    have hx2 : x ^ 2 > 0 := sq_pos_of_ne_zero hx
    rw [Real.log_div (by positivity) hx2.ne', show x ^ 2 = |x| ^ 2 by rw [sq_abs],
      Real.log_pow, Nat.cast_ofNat]
  have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x; simp
  rw [← integrableOn_univ, ← huniv]
  exact (h_Iio.union h_Icc).union h_Ioi

lemma kernelK_integrable_pi_half : Integrable (fun x : ℝ => kernelK (Real.pi / 2) x) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => kernelK (Real.pi / 2) x) volume := by
    unfold kernelK
    fun_prop
  have h_Icc : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Icc (-1 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.pi / 2 + 1) (Set.Icc (-1 : ℝ) 1) :=
      continuousOn_const.integrableOn_Icc
    refine hconst.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    unfold kernelK
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, zero_mul, neg_zero, zero_add,
      one_mul, Real.norm_eq_abs]
    have harctan : |Real.arctan (1 / x)| ≤ Real.pi / 2 :=
      abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    have hfrac : |x / (x ^ 2 + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + 1)]
      have hx_le : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
      have hden : 1 ≤ x ^ 2 + 1 := by linarith [sq_nonneg x]
      exact div_le_one_of_le₀ (hx_le.trans hden) (by positivity)
    calc |Real.arctan (1 / x) - x / (x ^ 2 + 1)|
        ≤ |Real.arctan (1 / x)| + |x / (x ^ 2 + 1)| := abs_sub _ _
      _ ≤ Real.pi / 2 + 1 := add_le_add harctan hfrac
  have h_Ioi : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Ioi (1 : ℝ)) := by
    have hpow : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 2
    refine hpow.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx_pos : 0 < x := by linarith
    have hu_pos : 0 < 1 / x := div_pos one_pos hx_pos
    have harctan_le : Real.arctan (1 / x) ≤ 1 / x := by
      have hmono : MonotoneOn (fun t : ℝ => t - Real.arctan t) (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact (continuous_id.sub Real.continuous_arctan).continuousOn
        · exact fun t _ => (differentiableAt_id.sub (Real.differentiableAt_arctan t)).differentiableWithinAt
        · intro t _
          have h1 : HasDerivAt (fun s : ℝ => s - Real.arctan s) (1 - 1 / (1 + t ^ 2)) t :=
            (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
          rw [h1.deriv]
          have hle : 1 / (1 + t ^ 2) ≤ 1 := div_le_one_of_le₀ (by linarith [sq_nonneg t]) (by positivity)
          linarith
      have := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hu_pos.le hu_pos.le
      simp only [sub_zero, Real.arctan_zero] at this
      linarith
    have harctan_ge : 1 / x - (1 / x) ^ 2 / 2 ≤ Real.arctan (1 / x) := by
      have hmono : MonotoneOn (fun t : ℝ => Real.arctan t - (t - t ^ 2 / 2)) (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact (Real.continuous_arctan.sub (continuous_id.sub ((continuous_pow 2).div_const 2))).continuousOn
        · intro t _
          exact ((Real.differentiableAt_arctan t).sub
            (differentiableAt_id.sub ((differentiableAt_pow 2).div_const 2))).differentiableWithinAt
        · intro t ht
          have ht0 : 0 ≤ t := interior_subset ht
          have h1 : HasDerivAt (fun s : ℝ => Real.arctan s - (s - s ^ 2 / 2))
              (1 / (1 + t ^ 2) - (1 - t)) t := by
            have ha := Real.hasDerivAt_arctan t
            have hb := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
            have hsub := ha.sub hb
            have hder : 1 / (1 + t ^ 2) - (1 - (2 : ℕ) * t ^ (2 - 1) / 2) = 1 / (1 + t ^ 2) - (1 - t) := by
              norm_num
            rw [hder] at hsub
            exact hsub
          rw [h1.deriv]
          have hpos : 0 ≤ t * (t ^ 2 - t + 1) := by
            have : t ^ 2 - t + 1 = (t - 1 / 2) ^ 2 + 3 / 4 := by ring
            nlinarith [sq_nonneg (t - 1 / 2)]
          have heq : 1 / (1 + t ^ 2) - (1 - t) = t * (t ^ 2 - t + 1) / (1 + t ^ 2) := by
            field_simp; ring
          rw [heq]
          exact div_nonneg hpos (by positivity)
      have := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hu_pos.le hu_pos.le
      simp only [Real.arctan_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_div] at this
      linarith
    have hdiff1 : |Real.arctan (1 / x) - 1 / x| ≤ 1 / x ^ 2 := by
      rw [abs_le]
      have hhalf : (1 / x) ^ 2 / 2 ≤ 1 / x ^ 2 := by
        rw [div_pow, one_pow, div_div]
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_pos_of_pos hx_pos])
      constructor <;> linarith
    have hdiff2 : |1 / x - x / (x ^ 2 + 1)| ≤ 1 / x ^ 2 := by
      have heq : 1 / x - x / (x ^ 2 + 1) = 1 / (x * (x ^ 2 + 1)) := by field_simp; ring
      rw [heq, abs_of_pos (div_pos one_pos (mul_pos hx_pos (by positivity)))]
      have hden : x ^ 2 ≤ x * (x ^ 2 + 1) := by nlinarith
      exact one_div_le_one_div_of_le (sq_pos_of_pos hx_pos) hden
    unfold kernelK
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, zero_mul, neg_zero, zero_add,
      one_mul, Real.norm_eq_abs]
    have hrpow : 2 * x ^ (-2 : ℝ) = 2 * (1 / x ^ 2) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
    rw [hrpow]
    calc |Real.arctan (1 / x) - x / (x ^ 2 + 1)|
        = |(Real.arctan (1 / x) - 1 / x) + (1 / x - x / (x ^ 2 + 1))| := by ring_nf
      _ ≤ |Real.arctan (1 / x) - 1 / x| + |1 / x - x / (x ^ 2 + 1)| := abs_add_le _ _
      _ ≤ 1 / x ^ 2 + 1 / x ^ 2 := add_le_add hdiff1 hdiff2
      _ = 2 * (1 / x ^ 2) := by ring
  have h_Iio : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Iio (-1 : ℝ)) := by
    have h_odd : ∀ x : ℝ, kernelK (Real.pi / 2) (-x) = -kernelK (Real.pi / 2) x := by
      intro x; unfold kernelK
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.arctan_neg, div_neg, neg_div]
      ring
    have hcomp : IntegrableOn (fun x : ℝ => -kernelK (Real.pi / 2) (-x)) (Set.Ioi (1 : ℝ)) := by
      simpa [h_odd] using h_Ioi
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by
      ext x; simp
    simpa [hpre] using hcomp.neg.comp_neg
  have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x; simp
  rw [← integrableOn_univ, ← huniv]
  exact (h_Iio.union h_Icc).union h_Ioi

lemma kernelK_integrable (θ : ℝ) : Integrable (fun x : ℝ => kernelK θ x) := by
  have h : (fun x : ℝ => kernelK θ x) =
      (fun x : ℝ => Real.cos θ * kernelK 0 x + Real.sin θ * kernelK (Real.pi / 2) x) := by
    ext x
    unfold kernelK
    simp [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [h]
  exact (kernelK_integrable_zero.const_mul _).add (kernelK_integrable_pi_half.const_mul _)

/-- **Lemma 2.3 (Part 1)**: Explicit Fourier transform `K̂_θ(ξ)` for `θ ∈ [-π/2, π/2]` and `ξ ≠ 0`,
together with `K̂_θ(0) = -π cos θ`. -/
lemma fourierHat_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    fourierHat f ξ = 𝓕 f ξ := by
  unfold fourierHat
  rw [Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm, RCLike.inner_apply, conj_trivial]
  congr 1
  push_cast
  ring

lemma fourierInv_eq_fourierHat_neg (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕⁻ f ξ = fourierHat f (-ξ) := by
  unfold fourierHat
  rw [Real.fourierInv_eq]
  congr 1; ext x
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm, RCLike.inner_apply, conj_trivial]
  congr 1
  push_cast
  ring

lemma integral_Iio_zero_eq_Ioi (F : ℝ → ℂ) :
    (∫ y in Set.Iio (0 : ℝ), F y) = ∫ y in Set.Ioi (0 : ℝ), F (-y) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iio,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← integral_neg_eq_self (μ := volume) (fun y : ℝ => (Set.Iio (0 : ℝ)).indicator F y)]
  congr 1; ext y
  by_cases hy : 0 < y
  · have h1 : -y ∈ Set.Iio (0 : ℝ) := by simp; linarith
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ioi.mpr hy)]
  · have h1 : -y ∉ Set.Iio (0 : ℝ) := by simp; linarith
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hy)]

lemma kernelK_zero_lorentz_fourier (u : ℝ) (hu : 0 < u) (ξ : ℝ) :
    fourierHat (fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) ξ =
      (Real.pi : ℂ) * Complex.exp (-2 * Real.pi * u * |ξ|) := by
  let g : ℝ → ℂ := fun y => (Real.pi : ℂ) * Complex.exp ((-2 * Real.pi * u * |y| : ℝ) : ℂ)
  have hg_cont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hg_int_Ioi : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun y : ℝ => Complex.exp ((-2 * Real.pi * u : ℂ) * y)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
    refine IntegrableOn.congr_fun (h1.const_mul (Real.pi : ℂ)) ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    dsimp only [g]
    rw [abs_of_pos hy0]
    congr 2; push_cast; ring
  have hg_int_Iio : IntegrableOn g (Set.Iio (0 : ℝ)) := by
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by ext y; simp
    have hcomp : IntegrableOn (fun y : ℝ => g (-y)) (Set.Iio (0 : ℝ)) := by
      simpa [hpre] using hg_int_Ioi.comp_neg
    refine hcomp.congr_fun ?_ measurableSet_Iio
    intro y _
    dsimp only [g]
    simp [abs_neg]
  have hg_int : Integrable g := by
    rw [← integrableOn_univ]
    have hIic : IntegrableOn g (Set.Iic (0 : ℝ)) := hg_int_Iio.congr_set_ae Iio_ae_eq_Iic.symm
    have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by ext y; simp [le_or_gt]
    rw [← huniv]
    exact hIic.union hg_int_Ioi
  have hFg : ∀ x : ℝ, 𝓕 g x = ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [← fourierHat_eq_fourier]
    unfold fourierHat
    have h_int_exp : Integrable (fun y : ℝ => g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      refine hg_int.norm.mono (by fun_prop) ?_
      filter_upwards with y
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * x * y)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑x * ↑y = ((-2 * Real.pi * x * y : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hn, mul_one, norm_norm]
    have hIic_eq : (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        ∫ y in Set.Iio (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y) :=
      setIntegral_congr_set Iio_ae_eq_Iic.symm
    have hsplit : (∫ y : ℝ, g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) +
        (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      have hc : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by ext y; simp
      rw [← hc]
      exact (integral_add_compl measurableSet_Ioi h_int_exp).symm.trans (add_comm _ _)
    rw [hsplit, hIic_eq, integral_Iio_zero_eq_Ioi]
    set c₁ : ℂ := -2 * Real.pi * u - 2 * Real.pi * Complex.I * x
    set c₂ : ℂ := -2 * Real.pi * u + 2 * Real.pi * Complex.I * x
    have hc₁_re : c₁.re < 0 := by simp [c₁]; positivity
    have hc₂_re : c₂.re < 0 := by simp [c₂]; positivity
    have hI1 : (∫ y in Set.Ioi (0 : ℝ), g (-y) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ))) =
        (Real.pi : ℂ) * (-1 / c₂) := by
      have heq : Set.EqOn (fun y : ℝ => g (-y) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ)))
          (fun y : ℝ => (Real.pi : ℂ) * Complex.exp (c₂ * y)) (Set.Ioi 0) := by
        intro y hy
        have hy0 : 0 < y := hy
        dsimp only [g, c₂]
        rw [abs_neg, abs_of_pos hy0, mul_assoc, ← Complex.exp_add]
        congr 2; push_cast; ring
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
        integral_exp_mul_complex_Ioi hc₂_re 0]
      simp
    have hI2 : (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        (Real.pi : ℂ) * (-1 / c₁) := by
      have heq : Set.EqOn (fun y : ℝ => g y * Complex.exp (-2 * Real.pi * Complex.I * x * y))
          (fun y : ℝ => (Real.pi : ℂ) * Complex.exp (c₁ * y)) (Set.Ioi 0) := by
        intro y hy
        have hy0 : 0 < y := hy
        dsimp only [g, c₁]
        rw [abs_of_pos hy0, mul_assoc, ← Complex.exp_add]
        congr 2; push_cast; ring
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
        integral_exp_mul_complex_Ioi hc₁_re 0]
      simp
    rw [hI1, hI2]
    have hc₁_ne : c₁ ≠ 0 := by intro h; rw [h] at hc₁_re; simp at hc₁_re
    have hc₂_ne : c₂ ≠ 0 := by intro h; rw [h] at hc₂_re; simp at hc₂_re
    have hden : (x ^ 2 + u ^ 2 : ℂ) ≠ 0 := by
      norm_cast
      positivity
    dsimp only [c₁, c₂] at *
    have hc₁' : (-↑u - Complex.I * ↑x : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    have hc₂' : (-↑u + Complex.I * ↑x : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    have hden' : (u ^ 2 + x ^ 2 : ℂ) ≠ 0 := by norm_cast; positivity
    field_simp [Real.pi_ne_zero, hc₁_ne, hc₂_ne, hden, hden']
    field_simp [hc₁', hc₂', hden, hden']
    simp only [Complex.I_sq]
    push_cast; ring
  have hFg_int : Integrable (𝓕 g) := by
    have heq : 𝓕 g = fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ) := funext hFg
    rw [heq]
    have hreal : Integrable (fun x : ℝ => u / (x ^ 2 + u ^ 2)) := by
      have hr : (1 / u : ℝ) ≠ 0 := by positivity
      have h1 := (integrable_inv_one_add_mul_sq hr).const_mul (1 / u)
      refine h1.congr (ae_of_all _ fun x => ?_)
      field_simp [hu.ne']; ring
    exact hreal.ofReal
  have hinv := congr_fun (Continuous.fourierInv_fourier_eq hg_cont hg_int hFg_int) (-ξ)
  rw [fourierInv_eq_fourierHat_neg, neg_neg] at hinv
  have heq_f : fourierHat (𝓕 g) ξ = fourierHat (fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) ξ := by
    unfold fourierHat
    congr 1; ext x
    rw [hFg x]
  rw [← heq_f, hinv]
  dsimp only [g]
  rw [abs_neg]
  congr 2
  push_cast; ring

lemma kernelK_pi_half_lorentz_fourier (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (ξ : ℝ) :
    fourierHat (fun x : ℝ => ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) ξ =
      -Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else if ξ < 0 then -1 else 0) *
        (Complex.exp (-2 * Real.pi * u * |ξ|) - Complex.exp (-2 * Real.pi * |ξ|)) := by
  let sgnC : ℝ → ℂ := fun y => if 0 < y then 1 else if y < 0 then -1 else 0
  let g : ℝ → ℂ := fun y => -Complex.I * (Real.pi : ℂ) * sgnC y *
    (Complex.exp ((-2 * Real.pi * u * |y| : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * |y| : ℝ) : ℂ))
  have hg_cont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · have h_ev : g =ᶠ[nhds y] fun z => -Complex.I * (Real.pi : ℂ) * (-1) *
          (Complex.exp ((-2 * Real.pi * u * (-z) : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * (-z) : ℝ) : ℂ)) := by
        filter_upwards [eventually_lt_nhds hy] with z hz
        dsimp only [g, sgnC]
        rw [if_neg (not_lt.mpr hz.le), if_pos hz, abs_of_neg hz]
      exact (ContinuousAt.congr (by fun_prop) h_ev.symm)
    · rw [ContinuousAt]
      have h0 : g 0 = 0 := by simp [g, sgnC]
      rw [h0, Metric.tendsto_nhds_nhds]
      intro ε hε
      have hcont_diff : ContinuousAt (fun z : ℝ =>
          Complex.exp ((-2 * Real.pi * u * |z| : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * |z| : ℝ) : ℂ)) 0 := by
        fun_prop
      have h0_diff : Complex.exp ((-2 * Real.pi * u * |(0 : ℝ)| : ℝ) : ℂ) -
          Complex.exp ((-2 * Real.pi * |(0 : ℝ)| : ℝ) : ℂ) = 0 := by simp
      rw [ContinuousAt, h0_diff, Metric.tendsto_nhds_nhds] at hcont_diff
      obtain ⟨δ, hδ, hδ_bd⟩ := hcont_diff (ε / Real.pi) (by positivity)
      refine ⟨δ, hδ, fun z hz => ?_⟩
      have hsgn_norm : ‖sgnC z‖ ≤ 1 := by
        dsimp only [sgnC]; split_ifs <;> simp
      have hnorm : ‖g z‖ ≤ Real.pi * ‖Complex.exp ((-2 * Real.pi * u * |z| : ℝ) : ℂ) -
          Complex.exp ((-2 * Real.pi * |z| : ℝ) : ℂ)‖ := by
        dsimp only [g]
        rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        calc Real.pi * ‖sgnC z‖ * ‖_‖ ≤ Real.pi * 1 * ‖_‖ := by gcongr
          _ = Real.pi * ‖_‖ := by ring
      have hz' := hδ_bd hz
      rw [dist_zero_right] at hz' ⊢
      calc ‖g z‖ ≤ Real.pi * ‖_‖ := hnorm
        _ < Real.pi * (ε / Real.pi) := mul_lt_mul_of_pos_left hz' Real.pi_pos
        _ = ε := by field_simp [Real.pi_ne_zero]
    · have h_ev : g =ᶠ[nhds y] fun z => -Complex.I * (Real.pi : ℂ) * 1 *
          (Complex.exp ((-2 * Real.pi * u * z : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * z : ℝ) : ℂ)) := by
        filter_upwards [eventually_gt_nhds hy] with z hz
        dsimp only [g, sgnC]
        rw [if_pos hz, abs_of_pos hz]
      exact (ContinuousAt.congr (by fun_prop) h_ev.symm)
  have hg_int_Ioi : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun y : ℝ => Complex.exp ((-2 * Real.pi * u : ℂ) * y)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
    have h2 : IntegrableOn (fun y : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * y)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
    refine IntegrableOn.congr_fun ((h1.sub h2).const_mul (-Complex.I * (Real.pi : ℂ) * 1)) ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    dsimp only [g, sgnC, Pi.sub_apply]
    rw [if_pos hy0, abs_of_pos hy0]
    congr 1; congr 1 <;> congr 1 <;> push_cast <;> ring
  have hg_int_Iio : IntegrableOn g (Set.Iio (0 : ℝ)) := by
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by ext y; simp
    have hcomp : IntegrableOn (fun y : ℝ => -g (-y)) (Set.Iio (0 : ℝ)) := by
      simpa [hpre] using hg_int_Ioi.neg.comp_neg
    refine hcomp.congr_fun ?_ measurableSet_Iio
    intro y hy
    have hy0 : y < 0 := hy
    dsimp only [g, sgnC]
    rw [if_neg (not_lt.mpr hy0.le), if_pos hy0, if_pos (neg_pos.mpr hy0), abs_neg]
    ring
  have hg_int : Integrable g := by
    rw [← integrableOn_univ]
    have hIic : IntegrableOn g (Set.Iic (0 : ℝ)) := hg_int_Iio.congr_set_ae Iio_ae_eq_Iic.symm
    have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by ext y; simp [le_or_gt]
    rw [← huniv]
    exact hIic.union hg_int_Ioi
  have hFg : ∀ x : ℝ, 𝓕 g x = -((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ) := by
    intro x
    rw [← fourierHat_eq_fourier]
    unfold fourierHat
    have h_int_exp : Integrable (fun y : ℝ => g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      refine hg_int.norm.mono (by fun_prop) ?_
      filter_upwards with y
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * x * y)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑x * ↑y = ((-2 * Real.pi * x * y : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hn, mul_one, norm_norm]
    have hIic_eq : (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        ∫ y in Set.Iio (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y) :=
      setIntegral_congr_set Iio_ae_eq_Iic.symm
    have hsplit : (∫ y : ℝ, g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) +
        (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      have hc : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by ext y; simp
      rw [← hc]
      exact (integral_add_compl measurableSet_Ioi h_int_exp).symm.trans (add_comm _ _)
    rw [hsplit, hIic_eq, integral_Iio_zero_eq_Ioi]
    set cu1 : ℂ := -2 * Real.pi * u - 2 * Real.pi * Complex.I * x
    set cu2 : ℂ := -2 * Real.pi * u + 2 * Real.pi * Complex.I * x
    set c11 : ℂ := -2 * Real.pi - 2 * Real.pi * Complex.I * x
    set c12 : ℂ := -2 * Real.pi + 2 * Real.pi * Complex.I * x
    have hcu1_re : cu1.re < 0 := by simp [cu1]; positivity
    have hcu2_re : cu2.re < 0 := by simp [cu2]; positivity
    have hc11_re : c11.re < 0 := by simp [c11]; positivity
    have hc12_re : c12.re < 0 := by simp [c12]; positivity
    have hI1 : (∫ y in Set.Ioi (0 : ℝ), g (-y) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ))) =
        Complex.I * (Real.pi : ℂ) * (-1 / cu2 - (-1 / c12)) := by
      have heq : Set.EqOn (fun y : ℝ => g (-y) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ)))
          (fun y : ℝ => Complex.I * (Real.pi : ℂ) * (Complex.exp (cu2 * y) - Complex.exp (c12 * y))) (Set.Ioi 0) := by
        intro y hy
        have hy0 : 0 < y := hy
        dsimp only [g, sgnC, cu2, c12]
        rw [if_neg (not_lt.mpr (neg_lt_zero.mpr hy0).le), if_pos (neg_lt_zero.mpr hy0), abs_neg, abs_of_pos hy0]
        have he1 : Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ)) =
            Complex.exp (cu2 * y) := by
          rw [← Complex.exp_add]; congr 1; dsimp only [cu2]; push_cast; ring
        have he2 : Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ)) =
            Complex.exp (c12 * y) := by
          rw [← Complex.exp_add]; congr 1; dsimp only [c12]; push_cast; ring
        calc -Complex.I * (Real.pi : ℂ) * (-1) *
              (Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ)) *
              Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ))
            = Complex.I * (Real.pi : ℂ) *
                (Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ)) -
                 Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-y : ℝ) : ℂ))) := by ring
          _ = Complex.I * (Real.pi : ℂ) * (Complex.exp (cu2 * y) - Complex.exp (c12 * y)) := by rw [he1, he2]
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
        integral_sub (integrableOn_exp_mul_complex_Ioi hcu2_re 0) (integrableOn_exp_mul_complex_Ioi hc12_re 0),
        integral_exp_mul_complex_Ioi hcu2_re 0, integral_exp_mul_complex_Ioi hc12_re 0]
      simp
    have hI2 : (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        -Complex.I * (Real.pi : ℂ) * (-1 / cu1 - (-1 / c11)) := by
      have heq : Set.EqOn (fun y : ℝ => g y * Complex.exp (-2 * Real.pi * Complex.I * x * y))
          (fun y : ℝ => -Complex.I * (Real.pi : ℂ) * (Complex.exp (cu1 * y) - Complex.exp (c11 * y))) (Set.Ioi 0) := by
        intro y hy
        have hy0 : 0 < y := hy
        dsimp only [g, sgnC, cu1, c11]
        rw [if_pos hy0, abs_of_pos hy0]
        have he1 : Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * y) =
            Complex.exp (cu1 * y) := by
          rw [← Complex.exp_add]; congr 1; dsimp only [cu1]; push_cast; ring
        have he2 : Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * y) =
            Complex.exp (c11 * y) := by
          rw [← Complex.exp_add]; congr 1; dsimp only [c11]; push_cast; ring
        calc -Complex.I * (Real.pi : ℂ) * 1 *
              (Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) - Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ)) *
              Complex.exp (-2 * Real.pi * Complex.I * x * y)
            = -Complex.I * (Real.pi : ℂ) *
                (Complex.exp ((-2 * Real.pi * u * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * y) -
                 Complex.exp ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by ring
          _ = -Complex.I * (Real.pi : ℂ) * (Complex.exp (cu1 * y) - Complex.exp (c11 * y)) := by rw [he1, he2]
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
        integral_sub (integrableOn_exp_mul_complex_Ioi hcu1_re 0) (integrableOn_exp_mul_complex_Ioi hc11_re 0),
        integral_exp_mul_complex_Ioi hcu1_re 0, integral_exp_mul_complex_Ioi hc11_re 0]
      simp
    rw [hI1, hI2]
    have hcu1_ne : cu1 ≠ 0 := by intro h; rw [h] at hcu1_re; simp at hcu1_re
    have hcu2_ne : cu2 ≠ 0 := by intro h; rw [h] at hcu2_re; simp at hcu2_re
    have hc11_ne : c11 ≠ 0 := by intro h; rw [h] at hc11_re; simp at hc11_re
    have hc12_ne : c12 ≠ 0 := by intro h; rw [h] at hc12_re; simp at hc12_re
    have hden : ((x ^ 2 + u ^ 2) * (x ^ 2 + 1) : ℂ) ≠ 0 := by
      norm_cast; positivity
    have d1 : (Complex.I * ↑x - ↑u : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    have d2 : (-1 + Complex.I * ↑x : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
    have d3 : (-(Complex.I * ↑x) - ↑u : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    have d4 : (-1 - Complex.I * ↑x : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
    dsimp only [cu1, cu2, c11, c12] at *
    have hden_exp : (x ^ 2 + x ^ 2 * u ^ 2 + x ^ 4 + u ^ 2 : ℂ) ≠ 0 := by
      have : (x ^ 2 + x ^ 2 * u ^ 2 + x ^ 4 + u ^ 2 : ℂ) = (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by ring
      rw [this]; exact hden
    field_simp [Real.pi_ne_zero, hcu1_ne, hcu2_ne, hc11_ne, hc12_ne, hden, d1, d2, d3, d4]
    field_simp [d1, d2, d3, d4, hden, hden_exp]
    have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    simp only [Complex.I_sq, hI3]
    push_cast; ring
  have hFg_int : Integrable (𝓕 g) := by
    have heq : 𝓕 g = fun x : ℝ => -((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ) := funext hFg
    rw [heq]
    have hreal : Integrable (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) := by
      have h_Ioi : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 1) := by
        have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
        refine hpow.mono' ((Continuous.aestronglyMeasurable ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div (by fun_prop) (fun x => by positivity))).restrict) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx1 : 1 < x := hx
        have hx_pos : 0 < x := by linarith
        have h1u : 0 ≤ 1 - u ^ 2 := by nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hx_pos.le h1u) (by positivity))]
        have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
          rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
        rw [hrpow]
        have hnum : x * (1 - u ^ 2) ≤ x := mul_le_of_le_one_right hx_pos.le (by nlinarith [sq_nonneg u])
        have hden : x ^ 3 ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by
          calc x ^ 3 = x ^ 2 * x := by ring
            _ ≤ x ^ 2 * x ^ 2 := by nlinarith
            _ ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by nlinarith [sq_nonneg u]
        calc x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))
            ≤ x / x ^ 3 := div_le_div₀ hx_pos.le hnum (by positivity) hden
          _ = 1 / x ^ 2 := by field_simp [hx_pos.ne']
      have h_Iio : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Iio (-1)) := by
        have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by ext x; simp
        have hcomp : IntegrableOn (fun x : ℝ => -((-x) * (1 - u ^ 2) / (((-x) ^ 2 + u ^ 2) * ((-x) ^ 2 + 1)))) (Set.Iio (-1)) := by
          simpa [hpre] using h_Ioi.neg.comp_neg
        refine hcomp.congr_fun (fun x _ => by ring) measurableSet_Iio
      have h_Icc : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Icc (-1) 1) := by
        refine ContinuousOn.integrableOn_Icc ?_
        refine Continuous.continuousOn ?_
        refine (by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div (by fun_prop) (fun x => by positivity)
      have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by ext x; simp
      rw [← integrableOn_univ, ← huniv]
      exact (h_Iio.union h_Icc).union h_Ioi
    exact (hreal.neg.ofReal).congr (ae_of_all _ fun x => by simp)
  have hinv := congr_fun (Continuous.fourierInv_fourier_eq hg_cont hg_int hFg_int) (-ξ)
  rw [fourierInv_eq_fourierHat_neg, neg_neg] at hinv
  have heq_f : fourierHat (𝓕 g) ξ =
      -fourierHat (fun x : ℝ => ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) ξ := by
    unfold fourierHat
    rw [← integral_neg]
    congr 1; ext x
    rw [hFg x]
    ring
  rw [heq_f] at hinv
  have hgn : -g (-ξ) = -Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else if ξ < 0 then -1 else 0) *
      (Complex.exp (-2 * Real.pi * u * |ξ|) - Complex.exp (-2 * Real.pi * |ξ|)) := by
    dsimp only [g, sgnC]
    rw [abs_neg]
    rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
    · rw [if_neg (not_lt.mpr hξ.le), if_pos hξ, if_pos (neg_pos.mpr hξ)]
      push_cast; ring
    · simp
    · rw [if_pos hξ, if_neg (not_lt.mpr (neg_lt_zero.mpr hξ).le), if_pos (neg_lt_zero.mpr hξ)]
      push_cast; ring
  have hres : fourierHat (fun x : ℝ => ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) ξ = -g (-ξ) := by
    linear_combination -hinv
  rw [hres, hgn]

private lemma kernelK_zero_four (ξ : ℝ) :
    fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) ξ =
      -∫ u in Set.Ioc (0 : ℝ) 1, fourierHat (fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) ξ := by
  let F : ℝ × ℝ → ℂ := fun p => ((p.2 / (p.1 ^ 2 + p.2 ^ 2) : ℝ) : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * ξ * p.1)
  have hF_meas : AEStronglyMeasurable F (volume.prod (volume.restrict (Set.Ioc 0 1))) := by
    dsimp only [F]
    fun_prop
  have hF_x_int : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), Integrable (fun x : ℝ => F (x, u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have hreal : Integrable (fun x : ℝ => u / (x ^ 2 + u ^ 2)) := by
      have hr : (1 / u : ℝ) ≠ 0 := by positivity
      refine ((integrable_inv_one_add_mul_sq hr).const_mul (1 / u)).congr (ae_of_all _ fun x => ?_)
      field_simp [hu0.ne']; ring
    refine hreal.norm.mono (by dsimp only [F]; fun_prop) ?_
    filter_upwards with x
    have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
      have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, hn, mul_one, norm_norm]
  have hF_u_int : Integrable (fun u : ℝ => ∫ x : ℝ, ‖F (x, u)‖) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have heq : Set.EqOn (fun u : ℝ => ∫ x : ℝ, ‖F (x, u)‖) (fun _ : ℝ => Real.pi) (Set.Ioc 0 1) := by
      intro u hu
      have hu0 : 0 < u := hu.1
      have h1 : ∀ x : ℝ, ‖F (x, u)‖ = (1 / u) * (1 + ((1 / u) * x) ^ 2)⁻¹ := by
        intro x
        have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
          have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        dsimp only [F]
        rw [norm_mul, Complex.norm_real, hn, mul_one, Real.norm_eq_abs,
          abs_of_pos (div_pos hu0 (by positivity))]
        field_simp [hu0.ne']; ring
      simp_rw [h1]
      rw [integral_const_mul, integral_univ_inv_one_add_mul_sq (1 / u)]
      rw [abs_of_pos (by positivity)]
      field_simp [hu0.ne']
    exact (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self : IntegrableOn (fun _ : ℝ => Real.pi) (Set.Ioc 0 1)).congr_fun
      heq.symm measurableSet_Ioc
  have hF_prod_int : Integrable F (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (integrable_prod_iff' hF_meas).mpr ⟨hF_x_int, hF_u_int⟩
  have h_inner_x : ∀ x : ℝ, x ≠ 0 →
      (∫ u in Set.Ioc (0 : ℝ) 1, F (x, u)) = -(kernelK 0 x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) := by
    intro x hx
    dsimp only [F]
    rw [integral_mul_const]
    have hreal_int : (∫ u in Set.Ioc (0 : ℝ) 1, u / (x ^ 2 + u ^ 2)) = -kernelK 0 x := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun v : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + v ^ 2)) (u / (x ^ 2 + u ^ 2)) u := by
        intro u _
        have hpos : x ^ 2 + u ^ 2 ≠ 0 := by positivity
        have hd := ((hasDerivAt_pow 2 u).const_add (x ^ 2)).log hpos
        convert hd.const_mul (1 / 2 : ℝ) using 1
        field_simp [hpos]; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
        apply ContinuousOn.intervalIntegrable
        exact Continuous.continuousOn (continuous_id.div (by fun_prop) (fun u => by positivity)))]
      unfold kernelK
      simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      rw [← mul_sub, ← Real.log_div (by positivity) (by positivity)]
      ring
    have hofReal : (∫ u in Set.Ioc (0 : ℝ) 1, ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) =
        ((∫ u in Set.Ioc (0 : ℝ) 1, u / (x ^ 2 + u ^ 2) : ℝ) : ℂ) := integral_ofReal
    rw [hofReal, hreal_int]
    push_cast; ring
  have hK_eq : fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) ξ =
      -∫ x : ℝ, ∫ u in Set.Ioc (0 : ℝ) 1, F (x, u) := by
    unfold fourierHat
    rw [← integral_neg]
    refine integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with x hx
    rw [h_inner_x x hx]
    ring
  rw [hK_eq, integral_integral_swap hF_prod_int]
  rfl

private lemma kernelK_pi_half_four (ξ : ℝ) (hξ : ξ ≠ 0) :
    fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) ξ =
      ∫ u in Set.Ioc (0 : ℝ) 1, fourierHat (fun x : ℝ => ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) ξ := by
  let F : ℝ × ℝ → ℂ := fun p =>
    ((p.1 * (1 - p.2 ^ 2) / ((p.1 ^ 2 + p.2 ^ 2) * (p.1 ^ 2 + 1)) : ℝ) : ℂ) *
      Complex.exp (-2 * Real.pi * Complex.I * ξ * p.1)
  have hF_meas : AEStronglyMeasurable F (volume.prod (volume.restrict (Set.Ioc 0 1))) := by
    dsimp only [F]; fun_prop
  have hF_x_int : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), Integrable (fun x : ℝ => F (x, u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hreal : Integrable (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) := by
      have h_Ioi : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 1) := by
        have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
        refine hpow.mono' ((Continuous.aestronglyMeasurable ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div (by fun_prop) (fun x => by positivity))).restrict) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx1 : 1 < x := hx
        have hx_pos : 0 < x := by linarith
        have h1u : 0 ≤ 1 - u ^ 2 := by nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hx_pos.le h1u) (by positivity))]
        have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
          rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
        rw [hrpow]
        have hnum : x * (1 - u ^ 2) ≤ x := mul_le_of_le_one_right hx_pos.le (by nlinarith [sq_nonneg u])
        have hden : x ^ 3 ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by
          calc x ^ 3 = x ^ 2 * x := by ring
            _ ≤ x ^ 2 * x ^ 2 := by nlinarith
            _ ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by nlinarith [sq_nonneg u]
        calc x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))
            ≤ x / x ^ 3 := div_le_div₀ hx_pos.le hnum (by positivity) hden
          _ = 1 / x ^ 2 := by field_simp [hx_pos.ne']
      have h_Iio : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Iio (-1)) := by
        have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by ext x; simp
        have hcomp : IntegrableOn (fun x : ℝ => -((-x) * (1 - u ^ 2) / (((-x) ^ 2 + u ^ 2) * ((-x) ^ 2 + 1)))) (Set.Iio (-1)) := by
          simpa [hpre] using h_Ioi.neg.comp_neg
        refine hcomp.congr_fun (fun x _ => by ring) measurableSet_Iio
      have h_Icc : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Icc (-1) 1) :=
        (Continuous.continuousOn ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div
          (by fun_prop) (fun x => by positivity))).integrableOn_Icc
      have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by ext x; simp
      rw [← integrableOn_univ, ← huniv]
      exact (h_Iio.union h_Icc).union h_Ioi
    refine hreal.norm.mono (by dsimp only [F]; fun_prop) ?_
    filter_upwards with x
    have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
      have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, hn, mul_one, norm_norm]
  have hF_u_int : Integrable (fun u : ℝ => ∫ x : ℝ, ‖F (x, u)‖) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have heq : Set.EqOn (fun u : ℝ => ∫ x : ℝ, ‖F (x, u)‖) (fun u : ℝ => -2 * Real.log u) (Set.Ioc 0 1) := by
      intro u hu
      have hu0 : 0 < u := hu.1
      have hu1 : u ≤ 1 := hu.2
      have h1u : 0 ≤ 1 - u ^ 2 := by nlinarith
      have h_norm : ∀ x : ℝ, ‖F (x, u)‖ = |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) := by
        intro x
        have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
          have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        dsimp only [F]
        have hden_pos : 0 < (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := mul_pos (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hu0)) (by positivity)
        rw [norm_mul, Complex.norm_real, hn, mul_one, Real.norm_eq_abs, abs_div, abs_mul,
          abs_of_nonneg h1u, abs_of_pos hden_pos]
      simp_rw [h_norm]
      have h_pos_int : (∫ x in Set.Ioi (0 : ℝ), x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) = -Real.log u := by
        have h_Ioi_int : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 0) := by
          have h01 : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioc 0 1) :=
            (Continuous.continuousOn ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div
              (by fun_prop) (fun x => by positivity))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
          have h1inf : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 1) := by
            have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
              integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
            refine hpow.mono' ((Continuous.aestronglyMeasurable ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div (by fun_prop) (fun x => by positivity))).restrict) ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            have hx1 : 1 < x := hx
            have hx_pos : 0 < x := by linarith
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hx_pos.le h1u) (by positivity))]
            have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
              rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
            rw [hrpow]
            have hnum : x * (1 - u ^ 2) ≤ x := mul_le_of_le_one_right hx_pos.le (by nlinarith [sq_nonneg u])
            have hden : x ^ 3 ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by
              calc x ^ 3 = x ^ 2 * x := by ring
                _ ≤ x ^ 2 * x ^ 2 := by nlinarith
                _ ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by nlinarith [sq_nonneg u]
            calc x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))
                ≤ x / x ^ 3 := div_le_div₀ hx_pos.le hnum (by positivity) hden
              _ = 1 / x ^ 2 := by field_simp [hx_pos.ne']
          have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
          rw [← hun]
          exact h01.union h1inf
        let G : ℝ → ℝ := fun x => (1 / 2 : ℝ) * Real.log ((x ^ 2 + u ^ 2) / (x ^ 2 + 1))
        have hG_cont : ContinuousAt G 0 := by
          dsimp only [G]
          refine Continuous.continuousAt ?_
          refine Continuous.const_mul (Continuous.log ?_ (fun x => by positivity)) _
          exact (by fun_prop : Continuous (fun x : ℝ => x ^ 2 + u ^ 2)).div (by fun_prop) (fun x => by positivity)
        have hG_deriv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt G (x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) x := by
          intro x _
          have hq : HasDerivAt (fun t : ℝ => (t ^ 2 + u ^ 2) / (t ^ 2 + 1))
              (((2 * x) * (x ^ 2 + 1) - (x ^ 2 + u ^ 2) * (2 * x)) / (x ^ 2 + 1) ^ 2) x := by
            have h1 := (hasDerivAt_pow 2 x).add_const (u ^ 2)
            have h2 := (hasDerivAt_pow 2 x).add_const (1 : ℝ)
            convert h1.div h2 (by positivity) using 1
            ring
          have hlog := hq.log (by positivity)
          convert hlog.const_mul (1 / 2 : ℝ) using 1
          field_simp; ring
        have hG_tend : Tendsto G atTop (nhds 0) := by
          have hlim : Tendsto (fun x : ℝ => (x ^ 2 + u ^ 2) / (x ^ 2 + 1)) atTop (nhds 1) := by
            have heq : ∀ᶠ x : ℝ in atTop, (x ^ 2 + u ^ 2) / (x ^ 2 + 1) = (1 + u ^ 2 / x ^ 2) / (1 + 1 / x ^ 2) := by
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
              field_simp [hx.ne']
            rw [tendsto_congr' heq]
            have hinv : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
              simpa [one_div] using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
            have hnum : Tendsto (fun x : ℝ => 1 + u ^ 2 / x ^ 2) atTop (nhds (1 + u ^ 2 * 0)) := by
              simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
            have hden : Tendsto (fun x : ℝ => 1 + 1 / x ^ 2) atTop (nhds (1 + 0)) :=
              tendsto_const_nhds.add hinv
            simpa using (Tendsto.div hnum hden (by norm_num)).congr (fun x => by simp [one_div])
          have hlog_lim := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hlim
          simpa [G, Real.log_one] using tendsto_const_nhds.mul hlog_lim
        have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hG_deriv h_Ioi_int hG_tend
        have hG0 : G 0 = Real.log u := by
          dsimp only [G]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, div_one]
          rw [Real.log_pow, Nat.cast_ofNat]; ring
        rw [hres, hG0, zero_sub]
      have h_real_int : Integrable (fun x : ℝ => |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) := by
        have h_Ioi : IntegrableOn (fun x : ℝ => |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 0) := by
          refine IntegrableOn.congr_fun ?_ (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
          have h01 : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioc 0 1) :=
            (Continuous.continuousOn ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div
              (by fun_prop) (fun x => by positivity))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
          have h1inf : IntegrableOn (fun x : ℝ => x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Ioi 1) := by
            have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
              integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
            refine hpow.mono' ((Continuous.aestronglyMeasurable ((by fun_prop : Continuous (fun x : ℝ => x * (1 - u ^ 2))).div (by fun_prop) (fun x => by positivity))).restrict) ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            have hx1 : 1 < x := hx
            have hx_pos : 0 < x := by linarith
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hx_pos.le h1u) (by positivity))]
            have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
              rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
            rw [hrpow]
            have hnum : x * (1 - u ^ 2) ≤ x := mul_le_of_le_one_right hx_pos.le (by nlinarith [sq_nonneg u])
            have hden : x ^ 3 ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by
              calc x ^ 3 = x ^ 2 * x := by ring
                _ ≤ x ^ 2 * x ^ 2 := by nlinarith
                _ ≤ (x ^ 2 + u ^ 2) * (x ^ 2 + 1) := by nlinarith [sq_nonneg u]
            calc x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))
                ≤ x / x ^ 3 := div_le_div₀ hx_pos.le hnum (by positivity) hden
              _ = 1 / x ^ 2 := by field_simp [hx_pos.ne']
          rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
          exact h01.union h1inf
        have h_Iio : IntegrableOn (fun x : ℝ => |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Iio 0) := by
          have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by ext x; simp
          have hcomp : IntegrableOn (fun x : ℝ => |-x| * (1 - u ^ 2) / (((-x) ^ 2 + u ^ 2) * ((-x) ^ 2 + 1))) (Set.Iio 0) := by
            simpa [hpre] using h_Ioi.comp_neg
          exact hcomp.congr_fun (fun x _ => by simp [abs_neg]) measurableSet_Iio
        rw [← integrableOn_univ]
        have hIic : IntegrableOn (fun x : ℝ => |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) (Set.Iic 0) :=
          h_Iio.congr_set_ae Iio_ae_eq_Iic.symm
        have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by ext x; simp [le_or_gt]
        rw [← huniv]
        exact hIic.union h_Ioi
      have hsplit : (∫ x : ℝ, |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) =
          (∫ x in Set.Iic (0 : ℝ), |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) +
          (∫ x in Set.Ioi (0 : ℝ), |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) := by
        have hc : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by ext x; simp
        rw [← hc]
        exact (integral_add_compl measurableSet_Ioi h_real_int).symm.trans (add_comm _ _)
      rw [hsplit, setIntegral_congr_set Iio_ae_eq_Iic.symm]
      have hIio_eq : (∫ x in Set.Iio (0 : ℝ), |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) =
          ∫ x in Set.Ioi (0 : ℝ), x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) := by
        rw [← MeasureTheory.integral_indicator measurableSet_Iio,
          ← MeasureTheory.integral_indicator measurableSet_Ioi,
          ← integral_neg_eq_self (μ := volume) (fun x : ℝ => (Set.Iio (0 : ℝ)).indicator (fun x => |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) x)]
        congr 1; ext x
        by_cases hx : 0 < x
        · have h1 : -x ∈ Set.Iio (0 : ℝ) := by simp; linarith
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ioi.mpr hx), abs_neg, abs_of_pos hx]
        · have h1 : -x ∉ Set.Iio (0 : ℝ) := by simp; linarith
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hx)]
      have hIoi_eq : (∫ x in Set.Ioi (0 : ℝ), |x| * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) =
          ∫ x in Set.Ioi (0 : ℝ), x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [abs_of_pos hx])
      rw [hIio_eq, hIoi_eq, h_pos_int]
      ring
    have hlog_int : IntegrableOn (fun u : ℝ => -2 * Real.log u) (Set.Ioc 0 1) := by
      have hrpow_ioc : IntegrableOn (fun x : ℝ => 2 * x ^ (-1 / 2 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2))).const_mul 2
      refine (hrpow_ioc.const_mul 2).mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu_pos : 0 < u := hu.1
      have h_inv : 0 < u ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hu_pos _
      have hlog_neg : Real.log u ≤ 0 := Real.log_nonpos hu_pos.le hu.2
      have hbound : -Real.log u ≤ 2 * u ^ (-1 / 2 : ℝ) := by
        have h1 : Real.log (u ^ (-1 / 2 : ℝ)) ≤ u ^ (-1 / 2 : ℝ) - 1 := Real.log_le_sub_one_of_pos h_inv
        rw [Real.log_rpow hu_pos] at h1
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    exact hlog_int.congr_fun heq.symm measurableSet_Ioc
  have hF_prod_int : Integrable F (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (integrable_prod_iff' hF_meas).mpr ⟨hF_x_int, hF_u_int⟩
  have h_inner_x : ∀ x : ℝ, x ≠ 0 →
      (∫ u in Set.Ioc (0 : ℝ) 1, F (x, u)) = (kernelK (Real.pi / 2) x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) := by
    intro x hx
    dsimp only [F]
    rw [integral_mul_const]
    have hreal_int : (∫ u in Set.Ioc (0 : ℝ) 1, x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1))) =
        kernelK (Real.pi / 2) x := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have hsplit_u : ∀ u : ℝ, x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) =
          x / (x ^ 2 + u ^ 2) - x / (x ^ 2 + 1) := by
        intro u
        have h1 : x ^ 2 + u ^ 2 ≠ 0 := by positivity
        have h2 : x ^ 2 + 1 ≠ 0 := by positivity
        field_simp [h1, h2]; ring
      simp_rw [hsplit_u]
      have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun v : ℝ => Real.arctan (v / x) - v * (x / (x ^ 2 + 1)))
            (x / (x ^ 2 + u ^ 2) - x / (x ^ 2 + 1)) u := by
        intro u _
        have ha := ((hasDerivAt_id u).div_const x).arctan
        have hb := (hasDerivAt_id u).mul_const (x / (x ^ 2 + 1))
        refine (ha.sub hb).congr_deriv ?_
        dsimp only [id_eq]
        field_simp [hx]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
        apply ContinuousOn.intervalIntegrable
        exact Continuous.continuousOn ((continuous_const.div (by fun_prop) (fun u => by positivity)).sub continuous_const))]
      unfold kernelK
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    have hofReal : (∫ u in Set.Ioc (0 : ℝ) 1, ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) =
        ((∫ u in Set.Ioc (0 : ℝ) 1, x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ) := integral_ofReal
    rw [hofReal, hreal_int]
  have hK_eq : fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) ξ =
      ∫ x : ℝ, ∫ u in Set.Ioc (0 : ℝ) 1, F (x, u) := by
    unfold fourierHat
    refine integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with x hx
    exact (h_inner_x x hx).symm
  rw [hK_eq, integral_integral_swap hF_prod_int]
  rfl

private lemma kernelK_zero_fourier :
    fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) 0 = (-Real.pi : ℂ) ∧
    ∀ ξ : ℝ, ξ ≠ 0 → fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) ξ =
      -((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) := by
  have hK0_four := kernelK_zero_four
  have hK0_zero : fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) 0 = (-Real.pi : ℂ) := by
    rw [hK0_four 0]
    have heq : Set.EqOn (fun u : ℝ => fourierHat (fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) 0)
        (fun _ : ℝ => (Real.pi : ℂ)) (Set.Ioc 0 1) := by
      intro u hu
      dsimp only
      rw [kernelK_zero_lorentz_fourier u hu.1 0]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioc heq, setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), sub_zero, one_smul]
  have hK0_nz : ∀ ξ : ℝ, ξ ≠ 0 → fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) ξ =
      -((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) := by
    intro ξ hξ
    rw [hK0_four ξ]
    have heq : Set.EqOn (fun u : ℝ => fourierHat (fun x : ℝ => ((u / (x ^ 2 + u ^ 2) : ℝ) : ℂ)) ξ)
        (fun u : ℝ => (Real.pi : ℂ) * Complex.exp (-2 * Real.pi * u * |ξ|)) (Set.Ioc 0 1) := by
      intro u hu
      exact kernelK_zero_lorentz_fourier u hu.1 ξ
    rw [setIntegral_congr_fun measurableSet_Ioc heq,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hξ_ne_r : |ξ| ≠ 0 := abs_ne_zero.mpr hξ
    have hξ_ne : ((|ξ| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ_ne_r
    have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun v : ℝ => -(1 / (2 * ((|ξ| : ℝ) : ℂ))) * Complex.exp (-2 * Real.pi * v * ((|ξ| : ℝ) : ℂ)))
          ((Real.pi : ℂ) * Complex.exp (-2 * Real.pi * u * ((|ξ| : ℝ) : ℂ))) u := by
      intro u _
      have hd1 : HasDerivAt (fun v : ℝ => (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) * v)
          (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) u := by
        simpa using (hasDerivAt_id u).ofReal_comp.const_mul (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ))
      have hd2 := hd1.cexp.const_mul (-(1 / (2 * ((|ξ| : ℝ) : ℂ))))
      convert hd2 using 1
      · ext v; congr 1; ring
      · field_simp [hξ_ne]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
      apply ContinuousOn.intervalIntegrable; exact Continuous.continuousOn (by fun_prop))]
    simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    field_simp [hξ_ne]
    ring
  exact ⟨hK0_zero, hK0_nz⟩

private lemma kernelK_pi_half_fourier :
    fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) 0 = 0 ∧
    ∀ ξ : ℝ, ξ ≠ 0 → fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) ξ =
      -Complex.I * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
        Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)) := by
  have hKpi_four := kernelK_pi_half_four
  have hKpi_zero : fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) 0 = 0 := by
    unfold fourierHat
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    have h_odd : ∀ x : ℝ, kernelK (Real.pi / 2) (-x) = -kernelK (Real.pi / 2) x := by
      intro x; unfold kernelK
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.arctan_neg, div_neg, neg_div]
      ring
    have heq : (∫ x : ℝ, (kernelK (Real.pi / 2) x : ℂ)) = -(∫ x : ℝ, (kernelK (Real.pi / 2) x : ℂ)) := by
      calc (∫ x : ℝ, (kernelK (Real.pi / 2) x : ℂ))
          = ∫ x : ℝ, (kernelK (Real.pi / 2) (-x) : ℂ) := (integral_neg_eq_self (μ := volume) (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ))).symm
        _ = ∫ x : ℝ, -(kernelK (Real.pi / 2) x : ℂ) := by congr 1; ext x; rw [h_odd]; simp
        _ = -(∫ x : ℝ, (kernelK (Real.pi / 2) x : ℂ)) := integral_neg _
    have h2 : (2 : ℂ) * ∫ x : ℝ, (kernelK (Real.pi / 2) x : ℂ) = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hKpi_nz : ∀ ξ : ℝ, ξ ≠ 0 → fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) ξ =
      -Complex.I * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
        Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)) := by
    intro ξ hξ
    rw [hKpi_four ξ hξ]
    have heq : Set.EqOn (fun u : ℝ => fourierHat (fun x : ℝ => ((x * (1 - u ^ 2) / ((x ^ 2 + u ^ 2) * (x ^ 2 + 1)) : ℝ) : ℂ)) ξ)
        (fun u : ℝ => -Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1) *
          (Complex.exp (-2 * Real.pi * u * |ξ|) - Complex.exp (-2 * Real.pi * |ξ|))) (Set.Ioo 0 1) := by
      intro u hu
      dsimp only
      rw [kernelK_pi_half_lorentz_fourier u hu.1 hu.2 ξ]
      by_cases hpos : 0 < ξ
      · simp [hpos]
      · have hneg : ξ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hξ
        simp [hpos, hneg]
    rw [← setIntegral_congr_set Ioo_ae_eq_Ioc, setIntegral_congr_fun measurableSet_Ioo heq,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have h_abs_ne_r : |ξ| ≠ 0 := abs_ne_zero.mpr hξ
    have h_abs_ne : ((|ξ| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h_abs_ne_r
    have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun v : ℝ => -Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1) *
            (-(1 / (2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ))) * Complex.exp (-2 * (Real.pi : ℂ) * v * ((|ξ| : ℝ) : ℂ)) -
              v * Complex.exp (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ))))
          (-Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1) *
            (Complex.exp (-2 * (Real.pi : ℂ) * u * ((|ξ| : ℝ) : ℂ)) - Complex.exp (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)))) u := by
      intro u _
      have hd1 : HasDerivAt (fun v : ℝ => (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) * v)
          (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) u := by
        simpa using (hasDerivAt_id u).ofReal_comp.const_mul (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ))
      have hd2 := hd1.cexp.const_mul (-(1 / (2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ))))
      have hd3 := (hasDerivAt_id u).ofReal_comp.mul_const (Complex.exp (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)))
      have hd4 := (hd2.sub hd3).const_mul (-Complex.I * (Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1))
      convert hd4 using 1
      · ext v; congr 2; congr 1; ring
      · field_simp [Real.pi_ne_zero, h_abs_ne]; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
      apply ContinuousOn.intervalIntegrable; exact Continuous.continuousOn (by fun_prop))]
    have hξ_ne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
    have habs_eq : (if 0 < ξ then (1 : ℂ) else -1) / ((|ξ| : ℝ) : ℂ) = 1 / (ξ : ℂ) := by
      split_ifs with hpos
      · rw [abs_of_pos hpos, one_div]
      · have hneg : ξ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hξ
        rw [abs_of_neg hneg]; push_cast; field_simp [hξ_ne]
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_zero, sub_zero,
      Complex.ofReal_one, one_mul]
    calc -Complex.I * ↑π * (if 0 < ξ then (1 : ℂ) else -1) *
          (-(1 / (2 * ↑π * ↑|ξ|)) * Complex.exp (-2 * ↑π * ↑|ξ|) - Complex.exp (-2 * ↑π * ↑|ξ|)) -
        -Complex.I * ↑π * (if 0 < ξ then (1 : ℂ) else -1) * -(1 / (2 * ↑π * ↑|ξ|))
        = -Complex.I * ((1 - Complex.exp (-2 * ↑π * ↑|ξ|)) / 2 * ((if 0 < ξ then (1 : ℂ) else -1) / ↑|ξ|) -
            ↑π * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * ↑π * ↑|ξ|)) := by
          set sgn_ξ : ℂ := if 0 < ξ then 1 else -1
          field_simp [Real.pi_ne_zero, h_abs_ne]; ring
      _ = -Complex.I * ((1 - Complex.exp (-2 * ↑π * ↑|ξ|)) / (2 * ↑ξ) -
            ↑π * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * ↑π * ↑|ξ|)) := by
          rw [habs_eq]; ring
  exact ⟨hKpi_zero, hKpi_nz⟩

theorem kernelK_fourier (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) 0 = (-Real.pi * Real.cos θ : ℂ) ∧
    ∀ ξ : ℝ, ξ ≠ 0 →
      fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ =
        -(Real.cos θ : ℂ) * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) -
          Complex.I * (Real.sin θ : ℂ) *
            ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
              Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)) := by
  obtain ⟨hK0_zero, hK0_nz⟩ := kernelK_zero_fourier
  obtain ⟨hKpi_zero, hKpi_nz⟩ := kernelK_pi_half_fourier
  have hK_lin : ∀ ξ : ℝ, fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ =
      (Real.cos θ : ℂ) * fourierHat (fun x : ℝ => (kernelK 0 x : ℂ)) ξ +
      (Real.sin θ : ℂ) * fourierHat (fun x : ℝ => (kernelK (Real.pi / 2) x : ℂ)) ξ := by
    intro ξ
    unfold fourierHat
    have h1 : Integrable (fun x : ℝ => (Real.cos θ : ℂ) * ((kernelK 0 x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x))) := by
      refine (kernelK_integrable_zero.norm.const_mul |Real.cos θ|).mono
        (((Complex.continuous_ofReal.comp_aestronglyMeasurable kernelK_integrable_zero.aestronglyMeasurable).mul (by fun_prop)).const_mul _) ?_
      filter_upwards with x
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hn, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    have h2 : Integrable (fun x : ℝ => (Real.sin θ : ℂ) * ((kernelK (Real.pi / 2) x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x))) := by
      refine (kernelK_integrable_pi_half.norm.const_mul |Real.sin θ|).mono
        (((Complex.continuous_ofReal.comp_aestronglyMeasurable kernelK_integrable_pi_half.aestronglyMeasurable).mul (by fun_prop)).const_mul _) ?_
      filter_upwards with x
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hn, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
    have hK_eq : ∀ x : ℝ, kernelK θ x = Real.cos θ * kernelK 0 x + Real.sin θ * kernelK (Real.pi / 2) x := by
      intro x; unfold kernelK
      simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_mul, one_mul, add_zero, zero_add]
      ring
    congr 1; ext x
    dsimp only
    rw [hK_eq x]
    push_cast; ring
  constructor
  · rw [hK_lin 0, hK0_zero, hKpi_zero]; ring
  · intro ξ hξ
    rw [hK_lin ξ, hK0_nz ξ hξ, hKpi_nz ξ hξ]; ring

/-- **Lemma 2.3 (Part 2)**: Fourier decay of any bandlimited `L^1`-close majorant `M_{θ,Δ}`
at `ξ = ± log p / (2π)`. -/
theorem majorant_fourier_decay (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_dec > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∀ (p : ℕ), Nat.Prime p →
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) ∧
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) := by
  refine ⟨max (4 * Real.pi) (max C_L1 1), by positivity, fun Δ M hΔ hInt hL1 p hp => ?_⟩
  set C_dec := max (4 * Real.pi) (max C_L1 1)
  have hK_int : Integrable (fun x : ℝ => kernelK θ x) := kernelK_integrable θ
  have hM_int : Integrable (fun x : ℝ => M x) := by
    have : (fun x : ℝ => M x) = (fun x : ℝ => (M x - kernelK θ x) + kernelK θ x) := by
      ext x; ring
    rw [this]
    exact hInt.add hK_int
  have h_bound_ξ : ∀ ξ : ℝ, ξ ≠ 0 → 1 / |ξ| = 2 * Real.pi / Real.log p →
      ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ‖ ≤ C_dec * (1 / Real.log p + 1 / Δ) := by
    intro ξ hξ hξ_abs
    have hK_four := (kernelK_fourier θ hθ).2 ξ hξ
    have h_exp_le : Real.exp (-2 * Real.pi * |ξ|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * Real.pi * |ξ| := by positivity
      linarith
    have h_exp_pos : 0 < Real.exp (-2 * Real.pi * |ξ|) := Real.exp_pos _
    have h_cexp_eq : Complex.exp (-2 * Real.pi * |ξ|) = (Real.exp (-2 * Real.pi * |ξ|) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑|ξ| : ℂ) = ((-2 * Real.pi * |ξ| : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    have h_one_sub : ‖(1 : ℂ) - Complex.exp (-2 * Real.pi * |ξ|)‖ ≤ 1 := by
      rw [h_cexp_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h_pi_exp : Real.pi * Real.exp (-2 * Real.pi * |ξ|) ≤ 1 / (2 * |ξ|) := by
      have h_lin : 2 * Real.pi * |ξ| ≤ Real.exp (2 * Real.pi * |ξ|) := by
        linarith [Real.add_one_le_exp (2 * Real.pi * |ξ|)]
      have h_pos : 0 < 2 * Real.pi * |ξ| := by positivity
      calc Real.pi * Real.exp (-2 * Real.pi * |ξ|)
          = Real.pi / Real.exp (2 * Real.pi * |ξ|) := by
            rw [show -2 * Real.pi * |ξ| = -(2 * Real.pi * |ξ|) by ring, Real.exp_neg, div_eq_mul_inv]
        _ ≤ Real.pi / (2 * Real.pi * |ξ|) := by gcongr
        _ = 1 / (2 * |ξ|) := by field_simp [Real.pi_ne_zero]
    have hK_norm : ‖fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ ≤ 3 / (2 * |ξ|) := by
      rw [hK_four]
      have h1 : ‖-(Real.cos θ : ℂ) * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|))‖ ≤
          1 / (2 * |ξ|) := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        calc |Real.cos θ| * ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)‖
            ≤ 1 * (1 / (2 * |ξ|)) := by
              gcongr
              · exact Real.abs_cos_le_one θ
              · rw [norm_div, show (2 : ℂ) * ↑|ξ| = ((2 * |ξ| : ℝ) : ℂ) by push_cast; ring,
                  Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |ξ|)]
                exact div_le_div_of_nonneg_right h_one_sub (by positivity)
          _ = 1 / (2 * |ξ|) := one_mul _
      have h2 : ‖Complex.I * (Real.sin θ : ℂ) *
            ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
              Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|))‖ ≤
          2 / (2 * |ξ|) := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
        have h2a : ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ)‖ ≤ 1 / (2 * |ξ|) := by
          rw [norm_div, show (2 : ℂ) * ↑ξ = ((2 * ξ : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right h_one_sub (by positivity)
        have h2b : ‖(Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)‖ ≤
            1 / (2 * |ξ|) := by
          have hsgn : ‖if 0 < ξ then (1 : ℂ) else -1‖ = 1 := by split_ifs <;> simp
          rw [norm_mul, norm_mul, hsgn, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, h_cexp_eq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos h_exp_pos]
          exact h_pi_exp
        have h2c : ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
            Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)‖ ≤
            2 / (2 * |ξ|) := by
          calc _ ≤ _ + _ := norm_sub_le _ _
            _ ≤ 1 / (2 * |ξ|) + 1 / (2 * |ξ|) := add_le_add h2a h2b
            _ = 2 / (2 * |ξ|) := by ring
        calc |Real.sin θ| * ‖_‖ ≤ 1 * (2 / (2 * |ξ|)) := mul_le_mul hsin h2c (norm_nonneg _) zero_le_one
          _ = 2 / (2 * |ξ|) := one_mul _
      calc ‖_ - _‖ ≤ ‖_‖ + ‖_‖ := norm_sub_le _ _
        _ ≤ 1 / (2 * |ξ|) + 2 / (2 * |ξ|) := add_le_add h1 h2
        _ = 3 / (2 * |ξ|) := by ring
    have hexp_norm : ∀ x : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
      intro x
      have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hdiff_norm : ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ -
        fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ ≤ C_L1 / Δ := by
      have hM_c : Integrable (fun x : ℝ => (M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
        refine (hM_int.norm).mono (by fun_prop) ?_
        filter_upwards with x
        rw [norm_mul, Complex.norm_real, hexp_norm x, mul_one, norm_norm]
      have hK_c : Integrable (fun x : ℝ => (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
        refine (hK_int.norm).mono (by fun_prop) ?_
        filter_upwards with x
        rw [norm_mul, Complex.norm_real, hexp_norm x, mul_one, norm_norm]
      unfold fourierHat
      rw [← integral_sub hM_c hK_c]
      calc ‖∫ x : ℝ, ((M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) -
            (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x))‖
          ≤ ∫ x : ℝ, ‖(M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) -
            (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x : ℝ, |M x - kernelK θ x| := by
            congr 1; ext x
            rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              hexp_norm x, mul_one]
        _ ≤ C_L1 / Δ := hL1
    have hK_p : 3 / (2 * |ξ|) ≤ C_dec * (1 / Real.log p) := by
      rw [show 3 / (2 * |ξ|) = (3 / 2) * (1 / |ξ|) by ring, hξ_abs]
      have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have h3pi : 3 * Real.pi ≤ C_dec := le_trans (by linarith [Real.pi_pos]) (le_max_left _ _)
      calc (3 / 2) * (2 * Real.pi / Real.log p) = (3 * Real.pi) * (1 / Real.log p) := by ring
        _ ≤ C_dec * (1 / Real.log p) := by gcongr
    have hCL1_le : C_L1 / Δ ≤ C_dec * (1 / Δ) := by
      have hCL1 : C_L1 ≤ C_dec := le_trans (le_max_left _ _) (le_max_right _ _)
      have hΔ_pos : 0 < Δ := by linarith
      calc C_L1 / Δ = C_L1 * (1 / Δ) := by ring
        _ ≤ C_dec * (1 / Δ) := by gcongr
    calc ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ‖
        ≤ ‖fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ +
          ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ - fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' (fourierHat (fun x : ℝ => (M x : ℂ)) ξ)
            (fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ)
      _ ≤ 3 / (2 * |ξ|) + C_L1 / Δ := add_le_add hK_norm hdiff_norm
      _ ≤ C_dec * (1 / Real.log p) + C_dec * (1 / Δ) := add_le_add hK_p hCL1_le
      _ = C_dec * (1 / Real.log p + 1 / Δ) := by ring
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hξ_pos : 0 < Real.log p / (2 * Real.pi) := div_pos hlogp_pos (by positivity)
  refine ⟨h_bound_ξ _ hξ_pos.ne' ?_, h_bound_ξ _ (neg_ne_zero.mpr hξ_pos.ne') ?_⟩
  · rw [abs_of_pos hξ_pos, one_div_div]
  · rw [abs_neg, abs_of_pos hξ_pos, one_div_div]

end PolarEvaluation
