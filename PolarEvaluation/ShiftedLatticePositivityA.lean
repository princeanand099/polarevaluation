import PolarEvaluation.ShiftedLatticeContour

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

lemma summable_one_div_sq_nat : Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
  have h := Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  rw [← summable_nat_add_iff 1] at h
  refine h.congr fun n => ?_
  push_cast; ring

lemma tsum_int_split_gen {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℤ → E) (hp : Summable (fun n : ℕ => F (n + 1 : ℕ)))
    (hn : Summable (fun n : ℕ => F (-((n + 1 : ℕ) : ℤ)))) :
    Summable F ∧ ∑' m : ℤ, F m = F 0 + ∑' n : ℕ, (F (n + 1 : ℕ) + F (-((n + 1 : ℕ) : ℤ))) := by
  let e : ℕ ⊕ ℕ ⊕ Unit ≃ ℤ :=
    { toFun := fun s => match s with
        | Sum.inl n => (n + 1 : ℤ)
        | Sum.inr (Sum.inl n) => -((n + 1 : ℤ))
        | Sum.inr (Sum.inr ()) => 0
      invFun := fun m =>
        if 0 < m then Sum.inl (m.natAbs - 1)
        else if m < 0 then Sum.inr (Sum.inl (m.natAbs - 1))
        else Sum.inr (Sum.inr ())
      left_inv := fun s => by
        rcases s with n | (n | ⟨⟩)
        · simp; omega
        · simp only [Left.neg_pos_iff, Int.natCast_add, Int.natCast_one, Int.neg_lt_zero,
            Int.natAbs_neg]; split_ifs with h1 <;> omega
        · simp
      right_inv := fun m => by
        split_ifs with h1 h2
        · simp; omega
        · simp; omega
        · omega }
  have hs_sum : Summable (F ∘ e) := by
    rw [summable_sum_iff]
    refine ⟨hp, ?_⟩
    rw [summable_sum_iff]
    exact ⟨hn, summable_fintype _⟩
  have hs : Summable F := (Equiv.summable_iff e).mp hs_sum
  refine ⟨hs, ?_⟩
  rw [← e.tsum_eq]
  have hs1 : Summable (fun s : ℕ ⊕ Unit => F (e (Sum.inr s))) := by
    rw [summable_sum_iff]
    exact ⟨hn, summable_fintype _⟩
  rw [tsum_sum hp hs1, tsum_sum hn (summable_fintype _), tsum_unique]
  dsimp only [e]
  rw [← tsum_add hp hn]
  abel

lemma tsum_two_t_div_sq_bd (t : ℝ) (ht : 1 ≤ t) :
    Real.pi - 2 / t ≤ ∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ∧
      ∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤ Real.pi := by
  have ht_pos : 0 < t := by linarith
  have h_summ : Summable (fun n : ℕ => 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
    refine (summable_one_div_sq_nat.mul_left (2 * t)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have : (n + 1 : ℝ) ^ 2 ≤ t ^ 2 + (n + 1 : ℝ) ^ 2 := by linarith [sq_nonneg t]
    calc 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤ 2 * t / (n + 1 : ℝ) ^ 2 := by gcongr
      _ = 2 * t * (1 / (n + 1 : ℝ) ^ 2) := by ring
  have h_step : ∀ n : ℕ,
      2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤
        ∫ u in (n : ℝ)..(n + 1 : ℝ), 2 * t / (t ^ 2 + u ^ 2) ∧
      ∫ u in (n : ℝ)..(n + 1 : ℝ), 2 * t / (t ^ 2 + u ^ 2) ≤
        2 * t / (t ^ 2 + (n : ℝ) ^ 2) := by
    intro n
    have hcont : ContinuousOn (fun u : ℝ => 2 * t / (t ^ 2 + u ^ 2)) (Set.Icc (n : ℝ) (n + 1 : ℝ)) :=
      continuousOn_const.div (by fun_prop) (fun u _ => by positivity)
    have h_le : ∀ u ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ),
        2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤ 2 * t / (t ^ 2 + u ^ 2) ∧
        2 * t / (t ^ 2 + u ^ 2) ≤ 2 * t / (t ^ 2 + (n : ℝ) ^ 2) := by
      intro u hu
      have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg n) hu.1.le
      have hsq1 : u ^ 2 ≤ (n + 1 : ℝ) ^ 2 := sq_le_sq' (by linarith) hu.2
      have hsq2 : (n : ℝ) ^ 2 ≤ u ^ 2 := sq_le_sq' (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hu.1.le
      exact ⟨div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith),
             div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)⟩
    have h_len : (n + 1 : ℝ) - (n : ℝ) = 1 := by ring
    constructor
    · rw [intervalIntegral.integral_of_le (by linarith)]
      have h_c : ∫ _ in Set.Ioc (n : ℝ) (n + 1 : ℝ), 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) =
          2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul, h_len, one_mul]
      rw [← h_c]
      have h_c_int : IntegrableOn (fun _ : ℝ => 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) (Set.Ioc (n : ℝ) (n + 1 : ℝ)) :=
        (continuousOn_const : ContinuousOn (fun _ : ℝ => 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) (Set.Icc (n : ℝ) (n + 1 : ℝ))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      refine MeasureTheory.setIntegral_mono_on h_c_int
        (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        measurableSet_Ioc fun u hu => (h_le u hu).1
    · rw [intervalIntegral.integral_of_le (by linarith)]
      have h_c : ∫ _ in Set.Ioc (n : ℝ) (n + 1 : ℝ), 2 * t / (t ^ 2 + (n : ℝ) ^ 2) =
          2 * t / (t ^ 2 + (n : ℝ) ^ 2) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul, h_len, one_mul]
      rw [← h_c]
      have h_c_int : IntegrableOn (fun _ : ℝ => 2 * t / (t ^ 2 + (n : ℝ) ^ 2)) (Set.Ioc (n : ℝ) (n + 1 : ℝ)) :=
        (continuousOn_const : ContinuousOn (fun _ : ℝ => 2 * t / (t ^ 2 + (n : ℝ) ^ 2)) (Set.Icc (n : ℝ) (n + 1 : ℝ))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      refine MeasureTheory.setIntegral_mono_on
        (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        h_c_int measurableSet_Ioc fun u hu => (h_le u hu).2
  have h_int_eval : ∀ N : ℕ, ∫ u in (0 : ℝ)..(N : ℝ), 2 * t / (t ^ 2 + u ^ 2) =
      2 * Real.arctan ((N : ℝ) / t) := by
    intro N
    have hd : ∀ u ∈ Set.uIcc (0 : ℝ) (N : ℝ),
        HasDerivAt (fun x : ℝ => 2 * Real.arctan (x / t)) (2 * t / (t ^ 2 + u ^ 2)) u := by
      intro u _
      have ha := ((hasDerivAt_id u).div_const t).arctan
      refine (ha.const_mul 2).congr_deriv ?_
      dsimp only [id]; field_simp [ht_pos.ne']; ring
    have hcont : ContinuousOn (fun u : ℝ => 2 * t / (t ^ 2 + u ^ 2)) (Set.uIcc (0 : ℝ) (N : ℝ)) :=
      continuousOn_const.div (by fun_prop) (fun u _ => by positivity)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
    simp [Real.arctan_zero]
  have h_sum_int : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, ∫ u in (n : ℝ)..(n + 1 : ℝ), 2 * t / (t ^ 2 + u ^ 2) =
        ∫ u in (0 : ℝ)..(N : ℝ), 2 * t / (t ^ 2 + u ^ 2) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hcont : ContinuousOn (fun u : ℝ => 2 * t / (t ^ 2 + u ^ 2)) (Set.Icc 0 (k + 1 : ℝ)) :=
        continuousOn_const.div (by fun_prop) (fun u _ => by positivity)
      rw [intervalIntegral.integral_add_adjacent_intervals
        ((hcont.mono (by rw [Set.uIcc_of_le (by positivity)]; exact Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable)
        ((hcont.mono (by rw [Set.uIcc_of_le (by linarith)]; exact Set.Icc_subset_Icc_left (Nat.cast_nonneg k))).intervalIntegrable)]
      simp
  have h_upper_N : ∀ N : ℕ, ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤ Real.pi := by
    intro N
    calc ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.range N, ∫ u in (n : ℝ)..(n + 1 : ℝ), 2 * t / (t ^ 2 + u ^ 2) :=
          Finset.sum_le_sum fun n _ => (h_step n).1
      _ = 2 * Real.arctan ((N : ℝ) / t) := by rw [h_sum_int, h_int_eval]
      _ ≤ 2 * (Real.pi / 2) := by gcongr; exact (Real.arctan_lt_pi_div_two _).le
      _ = Real.pi := by ring
  have h_lower_N : ∀ N : ℕ, 2 * Real.arctan ((N : ℝ) / t) - 2 / t ≤
      ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) := by
    intro N
    have h_le_sum : 2 * Real.arctan ((N : ℝ) / t) ≤
        ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n : ℝ) ^ 2) := by
      rw [← h_int_eval, ← h_sum_int]
      exact Finset.sum_le_sum fun n _ => (h_step n).2
    have h_shift : ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n : ℝ) ^ 2) ≤
        2 / t + ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) := by
      cases N with
      | zero => simp; positivity
      | succ k =>
        rw [Finset.sum_range_succ', Finset.sum_range_succ]
        simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
        have h0 : 2 * t / t ^ 2 = 2 / t := by field_simp [ht_pos.ne']
        have hk : 0 ≤ 2 * t / (t ^ 2 + (k + 1 : ℝ) ^ 2) := by positivity
        push_cast; linarith
    linarith
  have h_tend_N : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2))
      atTop (nhds (∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2))) :=
    h_summ.hasSum.tendsto_sum_nat
  have h_tend_atan : Tendsto (fun N : ℕ => 2 * Real.arctan ((N : ℝ) / t) - 2 / t)
      atTop (nhds (2 * (Real.pi / 2) - 2 / t)) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) / t) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const ht_pos
    have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    exact ((h2.const_mul 2).sub tendsto_const_nhds)
  constructor
  · have := le_of_tendsto_of_tendsto h_tend_atan h_tend_N (Eventually.of_forall h_lower_N)
    linarith
  · exact le_of_tendsto h_tend_N (Eventually.of_forall h_upper_N)

lemma tsum_two_t_div_sq_tendsto :
    Tendsto (fun t : ℝ => ∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) atTop (nhds Real.pi) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun t : ℝ => Real.pi - 2 / t) (h := fun _ : ℝ => Real.pi) ?_ tendsto_const_nhds ?_ ?_
  · have h_lim : Tendsto (fun t : ℝ => Real.pi - 2 / t) atTop (nhds (Real.pi - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    simpa using h_lim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (tsum_two_t_div_sq_bd t ht).1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (tsum_two_t_div_sq_bd t ht).2

lemma summable_inv_add_inv_complex {w : ℂ}
    (hw1 : ∀ n : ℕ, w - (n + 1 : ℕ) ≠ 0) (hw2 : ∀ n : ℕ, w + (n + 1 : ℕ) ≠ 0) :
    Summable (fun n : ℕ => 1 / (w - (n + 1 : ℕ)) + 1 / (w + (n + 1 : ℕ))) := by
  let K : ℕ := 2 * Nat.ceil ‖w‖ + 1
  rw [← summable_nat_add_iff K]
  have h_sub : Summable (fun n : ℕ => (8 * ‖w‖) * ((1 : ℝ) / (n + 1 : ℝ) ^ 2)) :=
    summable_one_div_sq_nat.mul_left (8 * ‖w‖)
  refine h_sub.of_norm_bounded fun n => ?_
  have h1 := hw1 (n + K)
  have h2 := hw2 (n + K)
  have heq : 1 / (w - (n + K + 1 : ℕ)) + 1 / (w + (n + K + 1 : ℕ)) =
      2 * w / ((w - (n + K + 1 : ℕ)) * (w + (n + K + 1 : ℕ))) := by
    push_cast at h1 h2 ⊢; field_simp [h1, h2]; ring
  have heq' : 1 / (w - ((n + K : ℕ) + 1 : ℕ)) + 1 / (w + ((n + K : ℕ) + 1 : ℕ)) =
      2 * w / ((w - (n + K + 1 : ℕ)) * (w + (n + K + 1 : ℕ))) := by
    convert heq using 2 <;> push_cast <;> ring
  rw [heq', norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  have hceil : ‖w‖ ≤ Nat.ceil ‖w‖ := Nat.le_ceil _
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hm_ge : (n + K + 1 : ℝ) / 2 ≤ (n + K + 1 : ℝ) - |w.re| := by
    have : (K : ℝ) = 2 * (Nat.ceil ‖w‖ : ℝ) + 1 := by dsimp only [K]; push_cast; ring
    linarith
  have hlb1 : (n + K + 1 : ℝ) / 2 ≤ ‖w - (n + K + 1 : ℕ)‖ := by
    have h_re := Complex.abs_re_le_norm (w - (n + K + 1 : ℕ))
    simp only [Complex.sub_re, Complex.natCast_re] at h_re
    have h_abs : (n + K + 1 : ℝ) - |w.re| ≤ |w.re - (n + K + 1 : ℝ)| := by
      rw [abs_sub_comm]; exact le_trans (sub_le_sub_left (le_abs_self _) _) (le_abs_self _)
    push_cast at h_re ⊢; linarith
  have hlb2 : (n + K + 1 : ℝ) / 2 ≤ ‖w + (n + K + 1 : ℕ)‖ := by
    have h_re := Complex.abs_re_le_norm (w + (n + K + 1 : ℕ))
    simp only [Complex.add_re, Complex.natCast_re] at h_re
    have h_abs : (n + K + 1 : ℝ) - |w.re| ≤ |w.re + (n + K + 1 : ℝ)| := by
      have := le_abs_self (w.re + (n + K + 1 : ℝ))
      have := neg_le_abs w.re
      linarith
    push_cast at h_re ⊢; linarith
  have h_prod : ((n + 1 : ℝ) / 2) ^ 2 ≤ ‖w - (n + K + 1 : ℕ)‖ * ‖w + (n + K + 1 : ℕ)‖ := by
    have hn1 : (n + 1 : ℝ) / 2 ≤ (n + K + 1 : ℝ) / 2 := by linarith
    calc ((n + 1 : ℝ) / 2) ^ 2 = ((n + 1 : ℝ) / 2) * ((n + 1 : ℝ) / 2) := sq _
      _ ≤ ‖w - (n + K + 1 : ℕ)‖ * ‖w + (n + K + 1 : ℕ)‖ :=
          mul_le_mul (hn1.trans hlb1) (hn1.trans hlb2) (by positivity) (norm_nonneg _)
  calc 2 * ‖w‖ / (‖w - (n + K + 1 : ℕ)‖ * ‖w + (n + K + 1 : ℕ)‖)
      ≤ 2 * ‖w‖ / ((n + 1 : ℝ) / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h_prod
    _ = (8 * ‖w‖) * ((1 : ℝ) / (n + 1 : ℝ) ^ 2) := by field_simp; ring

lemma pi_cot_tsum_eq {z : ℂ} (hz : 0 < z.im) :
    (Real.pi : ℂ) * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z) =
      1 / z + ∑' n : ℕ, (1 / (z - (n + 1 : ℕ)) + 1 / (z + (n + 1 : ℕ))) := by
  let w : ℝ → ℂ := fun t => z + Complex.I * t
  have hw_im : ∀ t : ℝ, -z.im / 2 < t → z.im / 2 < (w t).im := fun t ht => by
    dsimp only [w]; simp; linarith
  have hw_ne : ∀ t : ℝ, -z.im / 2 < t → ∀ m : ℤ, w t - m ≠ 0 := by
    intro t ht m h0
    have him := congr_arg Complex.im h0
    simp [w] at him
    linarith [hw_im t ht]
  have h_sin_ne : ∀ t : ℝ, -z.im / 2 < t → Complex.sin (Real.pi * w t) ≠ 0 := by
    intro t ht h0
    rw [Complex.sin_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    have him := congr_arg Complex.im hm
    have : 0 < (w t).im := lt_trans (by linarith) (hw_im t ht)
    have him' : Real.pi * (w t).im = 0 := by
      simpa [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    nlinarith [Real.pi_pos]
  let f : ℕ → ℝ → ℂ := fun n t => 1 / (w t - (n + 1 : ℕ)) + 1 / (w t + (n + 1 : ℕ))
  let f' : ℕ → ℝ → ℂ := fun n t =>
    -Complex.I * (1 / (w t - (n + 1 : ℕ)) ^ 2 + 1 / (w t + (n + 1 : ℕ)) ^ 2)
  let N₀ : ℕ := 2 * Nat.ceil |z.re| + 2
  let C_bd : ℝ := max (8 / z.im ^ 2 * (N₀ : ℝ) ^ 2) 8
  let u : ℕ → ℝ := fun n => C_bd / (n + 1 : ℝ) ^ 2
  have hu_summ : Summable u := by simpa only [u, mul_one_div] using summable_one_div_sq_nat.mul_left C_bd
  have h_norm_lb : ∀ (n : ℕ) (t : ℝ), -z.im / 2 < t →
      (1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 + 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2) ≤ C_bd / (n + 1 : ℝ) ^ 2 := by
    intro n t ht
    have him_lb1 : z.im / 2 ≤ ‖w t - (n + 1 : ℕ)‖ := by
      have := Complex.abs_im_le_norm (w t - (n + 1 : ℕ))
      simp only [w, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, one_mul, Complex.natCast_im,
        sub_zero] at this
      simp only [zero_add] at this
      have h1 : z.im / 2 < z.im + t := by simpa [w] using hw_im t ht
      linarith [le_abs_self (z.im + t)]
    have him_lb2 : z.im / 2 ≤ ‖w t + (n + 1 : ℕ)‖ := by
      have := Complex.abs_im_le_norm (w t + (n + 1 : ℕ))
      simp only [w, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, one_mul, Complex.natCast_im,
        zero_add] at this
      have h1 : z.im / 2 < z.im + t := by simpa [w] using hw_im t ht
      linarith [le_abs_self (z.im + t)]
    by_cases hn : n + 1 ≤ N₀
    · have h1 : 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 ≤ 4 / z.im ^ 2 := by
        have hsq : (z.im / 2) ^ 2 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith) him_lb1
        calc 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 ≤ 1 / (z.im / 2) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hsq
          _ = 4 / z.im ^ 2 := by ring
      have h2 : 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2 ≤ 4 / z.im ^ 2 := by
        have hsq : (z.im / 2) ^ 2 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith) him_lb2
        calc 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2 ≤ 1 / (z.im / 2) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hsq
          _ = 4 / z.im ^ 2 := by ring
      have hn_le : (n + 1 : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 :=
        sq_le_sq' (by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by exact_mod_cast hn)
      calc 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 + 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2
          ≤ 4 / z.im ^ 2 + 4 / z.im ^ 2 := add_le_add h1 h2
        _ = 8 / z.im ^ 2 := by ring
        _ = (8 / z.im ^ 2 * (N₀ : ℝ) ^ 2) * (1 / (N₀ : ℝ) ^ 2) := by
            field_simp [Nat.cast_ne_zero.mpr (by omega : N₀ ≠ 0)]
        _ ≤ (8 / z.im ^ 2 * (N₀ : ℝ) ^ 2) * (1 / (n + 1 : ℝ) ^ 2) := by gcongr
        _ ≤ C_bd / (n + 1 : ℝ) ^ 2 := by rw [mul_one_div]; gcongr; exact le_max_left _ _
    · have hgt : N₀ < n + 1 := not_le.mp hn
      have hceil : |z.re| ≤ Nat.ceil |z.re| := Nat.le_ceil _
      have hre_ge : (n + 1 : ℝ) / 2 ≤ (n + 1 : ℝ) - |z.re| := by
        have : (N₀ : ℝ) < n + 1 := by exact_mod_cast hgt
        dsimp only [N₀] at this
        push_cast at this
        linarith
      have hre_lb1 : (n + 1 : ℝ) / 2 ≤ ‖w t - (n + 1 : ℕ)‖ := by
        have h1 := Complex.abs_re_le_norm (w t - (n + 1 : ℕ))
        simp only [w, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.natCast_re] at h1
        have h2 : (n + 1 : ℝ) - |z.re| ≤ |(z.re - (n + 1 : ℝ))| := by
          rw [abs_sub_comm]; exact le_trans (sub_le_sub_left (le_abs_self _) _) (le_abs_self _)
        push_cast at h1 ⊢; linarith
      have hre_lb2 : (n + 1 : ℝ) / 2 ≤ ‖w t + (n + 1 : ℕ)‖ := by
        have h1 := Complex.abs_re_le_norm (w t + (n + 1 : ℕ))
        simp only [w, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.natCast_re] at h1
        have h2 : (n + 1 : ℝ) - |z.re| ≤ |z.re + (n + 1 : ℝ)| := by
          have := le_abs_self (z.re + (n + 1 : ℝ))
          have := neg_le_abs z.re
          linarith
        push_cast at h1 ⊢; linarith
      have h1 : 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 ≤ 4 / (n + 1 : ℝ) ^ 2 := by
        have hsq : ((n + 1 : ℝ) / 2) ^ 2 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t - (n + 1 : ℕ))]) hre_lb1
        calc 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 ≤ 1 / ((n + 1 : ℝ) / 2) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hsq
          _ = 4 / (n + 1 : ℝ) ^ 2 := by field_simp; ring
      have h2 : 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2 ≤ 4 / (n + 1 : ℝ) ^ 2 := by
        have hsq : ((n + 1 : ℝ) / 2) ^ 2 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t + (n + 1 : ℕ))]) hre_lb2
        calc 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2 ≤ 1 / ((n + 1 : ℝ) / 2) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hsq
          _ = 4 / (n + 1 : ℝ) ^ 2 := by field_simp; ring
      calc 1 / ‖w t - (n + 1 : ℕ)‖ ^ 2 + 1 / ‖w t + (n + 1 : ℕ)‖ ^ 2
          ≤ 4 / (n + 1 : ℝ) ^ 2 + 4 / (n + 1 : ℝ) ^ 2 := add_le_add h1 h2
        _ = 8 / (n + 1 : ℝ) ^ 2 := by ring
        _ ≤ C_bd / (n + 1 : ℝ) ^ 2 := by gcongr; exact le_max_right _ _
  have hf_summ : ∀ t ∈ Set.Ioi (-z.im / 2), Summable (fun n => f n t) := by
    intro t ht
    refine summable_inv_add_inv_complex (fun n => by simpa using hw_ne t ht (n + 1 : ℤ))
      (fun n => by have := hw_ne t ht (-(n + 1 : ℤ)); push_cast at this ⊢; convert this using 1; ring)
  have hf_deriv : ∀ n : ℕ, ∀ t ∈ Set.Ioi (-z.im / 2), HasDerivAt (f n) (f' n t) t := by
    intro n t ht
    have h1 : w t - (n + 1 : ℕ) ≠ 0 := by simpa using hw_ne t ht (n + 1 : ℤ)
    have h2 : w t + (n + 1 : ℕ) ≠ 0 := by
      have := hw_ne t ht (-(n + 1 : ℤ))
      push_cast at this ⊢; convert this using 1; ring
    have hw_d : HasDerivAt w Complex.I t :=
      ((hasDerivAt_const t z).add ((hasDerivAt_id t).ofReal_comp.const_mul Complex.I)).congr_deriv (by simp)
    have hd1 : HasDerivAt (fun s => 1 / (w s - (n + 1 : ℕ)))
        (-Complex.I / (w t - (n + 1 : ℕ)) ^ 2) t := by
      simpa only [one_div] using ((hw_d.sub (hasDerivAt_const t ((n + 1 : ℕ) : ℂ))).inv h1).congr_deriv (by simp only [Pi.sub_apply]; field_simp [h1]; ring)
    have hd2 : HasDerivAt (fun s => 1 / (w s + (n + 1 : ℕ)))
        (-Complex.I / (w t + (n + 1 : ℕ)) ^ 2) t := by
      simpa only [one_div] using ((hw_d.add (hasDerivAt_const t ((n + 1 : ℕ) : ℂ))).inv h2).congr_deriv (by simp only [Pi.add_apply]; field_simp [h2]; ring)
    refine (hd1.add hd2).congr_deriv ?_
    dsimp only [f']; ring
  have hf'_bd : ∀ n : ℕ, ∀ t ∈ Set.Ioi (-z.im / 2), ‖f' n t‖ ≤ u n := by
    intro n t ht
    dsimp only [f', u]
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_one, norm_pow, norm_div, norm_one, norm_pow]
    exact h_norm_lb n t ht
  let g : ℝ → ℂ := fun t =>
    1 / w t + ∑' n : ℕ, f n t - (Real.pi : ℂ) * Complex.cos (Real.pi * w t) / Complex.sin (Real.pi * w t)
  let ψ : ℝ → ℝ := fun s => Real.sqrt (s ^ 2 + 1) - 1
  let ψ' : ℝ → ℝ := fun s => s / Real.sqrt (s ^ 2 + 1)
  have hψ_nonneg : ∀ s : ℝ, 0 ≤ ψ s := fun s => by
    dsimp only [ψ]
    have : (1 : ℝ) ≤ Real.sqrt (s ^ 2 + 1) := by
      conv_lhs => rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith [sq_nonneg s])
    linarith
  have hψ_mem : ∀ s : ℝ, ψ s ∈ Set.Ioi (-z.im / 2) := fun s => by
    change -z.im / 2 < ψ s; linarith [hψ_nonneg s, hz]
  have hψ_deriv : ∀ s : ℝ, HasDerivAt ψ (ψ' s) s := fun s => by
    have hpos : s ^ 2 + 1 ≠ 0 := by positivity
    have hinner : HasDerivAt (fun r : ℝ => r ^ 2 + 1) (2 * s) s :=
      ((hasDerivAt_pow 2 s).add (hasDerivAt_const s 1)).congr_deriv (by ring)
    refine ((hinner.sqrt hpos).sub (hasDerivAt_const s 1)).congr_deriv ?_
    dsimp only [ψ']; field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < s ^ 2 + 1)]; ring
  have hψ'_bd : ∀ s : ℝ, |ψ' s| ≤ 1 := fun s => by
    dsimp only [ψ']
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (by positivity : 0 < s ^ 2 + 1))]
    rw [div_le_one (Real.sqrt_pos.mpr (by positivity : 0 < s ^ 2 + 1))]
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hgψ_deriv : ∀ s : ℝ, HasDerivAt (fun r => g (ψ r)) 0 s := by
    intro s
    have ht : ψ s ∈ Set.Ioi (-z.im / 2) := hψ_mem s
    have h0 : w (ψ s) ≠ 0 := by simpa using hw_ne (ψ s) ht 0
    have hw_d : HasDerivAt (fun r => w (ψ r)) (Complex.I * (ψ' s : ℂ)) s := by
      have h1 : HasDerivAt (fun r : ℝ => ((ψ r : ℝ) : ℂ)) ((ψ' s : ℝ) : ℂ) s :=
        (hψ_deriv s).ofReal_comp
      exact ((hasDerivAt_const s z).add (h1.const_mul Complex.I)).congr_deriv (by simp)
    have hd_0 : HasDerivAt (fun r => 1 / w (ψ r)) (-Complex.I * (ψ' s : ℂ) / (w (ψ s)) ^ 2) s := by
      simp only [one_div]
      exact (hw_d.inv h0).congr_deriv (by field_simp [h0])
    have hd_sum : HasDerivAt (fun r => ∑' n : ℕ, f n (ψ r)) (∑' n : ℕ, f' n (ψ s) * (ψ' s : ℂ)) s := by
      refine hasDerivAt_tsum (f := fun n r => f n (ψ r)) (f' := fun n r => f' n (ψ r) * (ψ' r : ℂ)) hu_summ ?_ ?_ (hf_summ (ψ s) (hψ_mem s)) s
      · intro n r
        exact (hf_deriv n (ψ r) (hψ_mem r)).comp r (hψ_deriv r)
      · intro n r
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖f' n (ψ r)‖ * |ψ' r| ≤ u n * 1 :=
              mul_le_mul (hf'_bd n (ψ r) (hψ_mem r)) (hψ'_bd r) (abs_nonneg _) (by positivity)
          _ = u n := mul_one _
    have hsin : Complex.sin (Real.pi * w (ψ s)) ≠ 0 := h_sin_ne (ψ s) ht
    have hd_cot : HasDerivAt (fun r => (Real.pi : ℂ) * Complex.cos (Real.pi * w (ψ r)) / Complex.sin (Real.pi * w (ψ r)))
        (-Complex.I * (ψ' s : ℂ) * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * w (ψ s)) ^ 2)) s := by
      have hpw : HasDerivAt (fun r => (Real.pi : ℂ) * w (ψ r)) ((Real.pi : ℂ) * (Complex.I * (ψ' s : ℂ))) s :=
        hw_d.const_mul (Real.pi : ℂ)
      have hcos_d : HasDerivAt (fun r => Complex.cos (Real.pi * w (ψ r)))
          (-Complex.sin (Real.pi * w (ψ s)) * ((Real.pi : ℂ) * (Complex.I * (ψ' s : ℂ)))) s :=
        (Complex.hasDerivAt_cos (Real.pi * w (ψ s))).comp s hpw
      have hsin_d : HasDerivAt (fun r => Complex.sin (Real.pi * w (ψ r)))
          (Complex.cos (Real.pi * w (ψ s)) * ((Real.pi : ℂ) * (Complex.I * (ψ' s : ℂ)))) s :=
        (Complex.hasDerivAt_sin (Real.pi * w (ψ s))).comp s hpw
      have hq := (hcos_d.const_mul (Real.pi : ℂ)).div hsin_d hsin
      refine hq.congr_deriv ?_
      have hcs := Complex.cos_sq_add_sin_sq (Real.pi * w (ψ s))
      field_simp [hsin]
      calc (Real.pi : ℂ) * (-Complex.sin (Real.pi * w (ψ s)) * ((Real.pi : ℂ) * (Complex.I * ↑(ψ' s)))) * Complex.sin (Real.pi * w (ψ s)) -
            (Real.pi : ℂ) * Complex.cos (Real.pi * w (ψ s)) * (Complex.cos (Real.pi * w (ψ s)) * ((Real.pi : ℂ) * (Complex.I * ↑(ψ' s))))
          = -Complex.I * ↑(ψ' s) * (Real.pi : ℂ) ^ 2 * (Complex.cos (Real.pi * w (ψ s)) ^ 2 + Complex.sin (Real.pi * w (ψ s)) ^ 2) := by ring
        _ = -Complex.I * ↑(ψ' s) * (Real.pi : ℂ) ^ 2 := by rw [hcs, mul_one]
    have h_tsum_f' : (-Complex.I * (ψ' s : ℂ) / (w (ψ s)) ^ 2) + (∑' n : ℕ, f' n (ψ s) * (ψ' s : ℂ)) =
        -Complex.I * (ψ' s : ℂ) * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * w (ψ s)) ^ 2) := by
      have hs_p : Summable (fun n : ℕ => (1 : ℂ) / (w (ψ s) - (n + 1 : ℕ)) ^ 2) := by
        refine hu_summ.of_norm_bounded fun n => ?_
        rw [norm_div, norm_one, norm_pow]
        exact le_trans (le_add_of_nonneg_right (by positivity)) (h_norm_lb n (ψ s) ht)
      have hs_n : Summable (fun n : ℕ => (1 : ℂ) / (w (ψ s) + (n + 1 : ℕ)) ^ 2) := by
        refine hu_summ.of_norm_bounded fun n => ?_
        rw [norm_div, norm_one, norm_pow]
        exact le_trans (le_add_of_nonneg_left (by positivity)) (h_norm_lb n (ψ s) ht)
      have hsp := tsum_int_split_gen (E := ℂ) (fun m : ℤ => (1 : ℂ) / (w (ψ s) - m) ^ 2)
        (by simpa using hs_p)
        (by refine hs_n.congr fun n => ?_; push_cast; ring)
      have h_tsum_Z := tsum_inv_sub_I_sq (w (ψ s)) (lt_trans (by positivity) (hw_im (ψ s) ht))
      rw [hsp.2] at h_tsum_Z
      have heq_f' : (∑' n : ℕ, f' n (ψ s) * (ψ' s : ℂ)) =
          -Complex.I * (ψ' s : ℂ) * ∑' n : ℕ, ((1 : ℂ) / (w (ψ s) - (n + 1 : ℕ)) ^ 2 + 1 / (w (ψ s) + (n + 1 : ℕ)) ^ 2) := by
        dsimp only [f']
        rw [show (fun n : ℕ => -Complex.I * (1 / (w (ψ s) - (n + 1 : ℕ)) ^ 2 + 1 / (w (ψ s) + (n + 1 : ℕ)) ^ 2) * ↑(ψ' s)) =
            (fun n : ℕ => (-Complex.I * ↑(ψ' s)) * (1 / (w (ψ s) - (n + 1 : ℕ)) ^ 2 + 1 / (w (ψ s) + (n + 1 : ℕ)) ^ 2)) by ext n; ring]
        rw [tsum_mul_left]
      rw [heq_f']
      have h_match : ∑' n : ℕ, ((1 : ℂ) / (w (ψ s) - (n + 1 : ℕ)) ^ 2 + 1 / (w (ψ s) + (n + 1 : ℕ)) ^ 2) =
          ∑' n : ℕ, (1 / (w (ψ s) - ((n + 1 : ℕ) : ℤ)) ^ 2 + 1 / (w (ψ s) - (-((n + 1 : ℕ) : ℤ))) ^ 2) := by
        congr 1; ext n; push_cast; ring
      rw [h_match]
      rw [show (1 : ℂ) / (w (ψ s) - (0 : ℤ)) ^ 2 = 1 / (w (ψ s)) ^ 2 by simp] at h_tsum_Z
      rw [← h_tsum_Z]; ring
    refine ((hd_0.add hd_sum).sub hd_cot).congr_deriv ?_
    rw [h_tsum_f', sub_self]
  have hg_const : ∀ t : ℝ, 0 ≤ t → g t = g 0 := by
    intro t ht
    let s := Real.sqrt ((t + 1) ^ 2 - 1)
    have hψs : ψ s = t := by
      dsimp only [ψ, s]
      rw [Real.sq_sqrt (by nlinarith), sub_add_cancel, Real.sqrt_sq (by linarith)]
      ring
    have hψ0 : ψ 0 = 0 := by dsimp only [ψ]; norm_num
    have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
      (fun r _ => hgψ_deriv r) intervalIntegrable_const
    simp only [intervalIntegral.integral_const, smul_zero] at h_ftc
    rw [← hψs, ← hψ0]
    exact (sub_eq_zero.mp h_ftc.symm)
  have h_cot_lim : Tendsto (fun t : ℝ => (Real.pi : ℂ) * Complex.cos (Real.pi * w t) / Complex.sin (Real.pi * w t))
      atTop (nhds (-Real.pi * Complex.I)) := by
    have heq : ∀ᶠ t : ℝ in atTop,
        (Real.pi : ℂ) * Complex.cos (Real.pi * w t) / Complex.sin (Real.pi * w t) =
          -Real.pi * Complex.I * (1 + Complex.exp (2 * Complex.I * Real.pi * w t)) /
            (1 - Complex.exp (2 * Complex.I * Real.pi * w t)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hsin' : Complex.sin (Real.pi * w t) ≠ 0 := h_sin_ne t (by linarith)
      have hcos_def : Complex.cos (Real.pi * w t) =
          (Complex.exp (Real.pi * w t * Complex.I) + Complex.exp (-(Real.pi * w t) * Complex.I)) / 2 := by
        unfold Complex.cos; ring_nf
      have hsin_def : Complex.sin (Real.pi * w t) =
          (Complex.exp (-(Real.pi * w t) * Complex.I) - Complex.exp (Real.pi * w t * Complex.I)) * Complex.I / 2 := by
        unfold Complex.sin; ring_nf
      rw [hcos_def, hsin_def]
      have h1 : Complex.exp (Real.pi * w t * Complex.I) * Complex.exp (Real.pi * w t * Complex.I) =
          Complex.exp (2 * Complex.I * Real.pi * w t) := by
        rw [← Complex.exp_add]; ring_nf
      have hne_exp : Complex.exp (Real.pi * w t * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have hsub_ne : 1 - Complex.exp (2 * Complex.I * Real.pi * w t) ≠ 0 := by
        intro h0
        apply hsin'
        rw [hsin_def]
        have hsq1 : Complex.exp (Real.pi * w t * Complex.I) * Complex.exp (Real.pi * w t * Complex.I) = 1 := by
          rw [h1]; exact (sub_eq_zero.mp h0).symm
        have h_inv : Complex.exp (-(Real.pi * w t) * Complex.I) = Complex.exp (Real.pi * w t * Complex.I) := by
          rw [show -(Real.pi * w t) * Complex.I = -(Real.pi * w t * Complex.I) by ring, Complex.exp_neg]
          exact inv_eq_of_mul_eq_one_left hsq1
        rw [h_inv, sub_self, zero_mul, zero_div]
      rw [show -(Real.pi * w t) * Complex.I = -(Real.pi * w t * Complex.I) by ring, Complex.exp_neg]
      have h1' : Complex.exp (Real.pi * w t * Complex.I) ^ 2 = Complex.exp (Real.pi * w t * Complex.I * 2) := by
        rw [sq, ← Complex.exp_add]; ring_nf
      field_simp [hne_exp, hsub_ne, Complex.I_ne_zero]
      rw [Complex.I_sq, h1']
      ring
    have h_exp_lim : Tendsto (fun t : ℝ => Complex.exp (2 * Complex.I * Real.pi * w t)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h_norm : (fun t : ℝ => ‖Complex.exp (2 * Complex.I * Real.pi * w t)‖) =
          fun t : ℝ => Real.exp (-2 * Real.pi * (z.im + t)) := by
        ext t
        rw [Complex.norm_exp]
        congr 1
        simp [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [h_norm]
      have h1 : Tendsto (fun t : ℝ => -2 * Real.pi * (z.im + t)) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -2 * Real.pi < 0)
          (tendsto_atTop_add_const_left atTop z.im tendsto_id)
      exact Real.tendsto_exp_atBot.comp h1
    have h_quot : Tendsto (fun t : ℝ => -Real.pi * Complex.I * (1 + Complex.exp (2 * Complex.I * Real.pi * w t)) /
        (1 - Complex.exp (2 * Complex.I * Real.pi * w t))) atTop
        (nhds (-Real.pi * Complex.I * (1 + 0) / (1 - 0))) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add h_exp_lim)).div
        (tendsto_const_nhds.sub h_exp_lim) (by norm_num))
    simp only [add_zero, mul_one, sub_zero, div_one] at h_quot
    exact h_quot.congr' (heq.mono fun _ h => h.symm)
  have h_sum_lim : Tendsto (fun t : ℝ => 1 / w t + ∑' n : ℕ, f n t) atTop (nhds (-Real.pi * Complex.I)) := by
    have h0_lim : Tendsto (fun t : ℝ => 1 / w t) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h_bnd : ∀ᶠ t : ℝ in atTop, ‖1 / w t‖ ≤ 1 / t := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
        rw [norm_div, norm_one]
        have him : t ≤ ‖w t‖ := by
          have := Complex.abs_im_le_norm (w t)
          simp only [w, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, add_zero, one_mul] at this
          linarith [le_abs_self (z.im + t), hz]
        exact div_le_div_of_nonneg_left zero_le_one (by linarith) him
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id) (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
    have h_diff_lim : Tendsto (fun t : ℝ =>
        (∑' n : ℕ, f n t) - (-Complex.I * ∑' n : ℕ, ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)))
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      let C_z : ℝ := 40 * (‖z‖ + ‖z‖ ^ 2 + 1)
      have h_bnd : ∀ᶠ t : ℝ in atTop,
          ‖(∑' n : ℕ, f n t) - (-Complex.I * ∑' n : ℕ, ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ))‖ ≤
            C_z * (Real.pi / (2 * t)) := by
        filter_upwards [eventually_ge_atTop (max (2 * ‖z‖ + 2) 2)] with t ht
        have ht1 : 2 * ‖z‖ + 2 ≤ t := le_trans (le_max_left _ _) ht
        have ht2 : 2 ≤ t := le_trans (le_max_right _ _) ht
        have ht_pos : 0 < t := by linarith
        have hs1 := hf_summ t (Set.mem_Ioi.mpr (by linarith [hz, ht2]))
        have hs_r : Summable (fun n : ℕ => 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
          refine (summable_one_div_sq_nat.mul_left (2 * t)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
          have : (n + 1 : ℝ) ^ 2 ≤ t ^ 2 + (n + 1 : ℝ) ^ 2 := by linarith [sq_nonneg t]
          calc 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) ≤ 2 * t / (n + 1 : ℝ) ^ 2 := by gcongr
            _ = 2 * t * (1 / (n + 1 : ℝ) ^ 2) := by ring
        have hs2' : Summable (fun n : ℕ => ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)) :=
          Complex.ofRealCLM.summable hs_r
        have hs2 : Summable (fun n : ℕ => -Complex.I * ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)) :=
          hs2'.mul_left (-Complex.I)
        rw [← hs2'.tsum_mul_left, ← Summable.tsum_sub hs1 hs2]
        have hs_r_inv : Summable (fun n : ℕ => 1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
          refine summable_one_div_sq_nat.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_nonneg t])
        have h_term_bd : ∀ n : ℕ,
            ‖f n t - (-Complex.I * ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ))‖ ≤
              C_z * (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
          intro n
          have h1 := hw_ne t (by linarith) (n + 1 : ℤ)
          have h2 := hw_ne t (by linarith) (-(n + 1 : ℤ))
          push_cast at h1 h2
          have h2' : w t + ((n : ℂ) + 1) ≠ 0 := by convert h2 using 1; ring
          have hden_r : (t ^ 2 + ((n + 1 : ℕ) : ℂ) ^ 2) ≠ 0 := by
            exact_mod_cast (by positivity : (0 : ℝ) < t ^ 2 + (n + 1 : ℝ) ^ 2).ne'
          have h_alg : f n t - (-Complex.I * ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)) =
              2 * (z * ((n + 1 : ℕ) : ℂ) ^ 2 - z * (t : ℂ) ^ 2 + Complex.I * t * z ^ 2) /
                ((w t - (n + 1 : ℕ)) * (w t + (n + 1 : ℕ)) * (t ^ 2 + ((n + 1 : ℕ) : ℂ) ^ 2)) := by
            dsimp only [f, w]
            push_cast
            have h1'' : z + Complex.I * t - ((n : ℂ) + 1) ≠ 0 := by convert h1 using 1
            have h2'' : z + Complex.I * t + ((n : ℂ) + 1) ≠ 0 := by convert h2' using 1
            have hden'' : (t : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2 ≠ 0 := by convert hden_r using 1; push_cast; ring
            field_simp [h1'', h2'', hden'']
            ring_nf; simp [Complex.I_sq]; ring
          rw [h_alg, norm_div]; simp_rw [norm_mul]; rw [Complex.norm_ofNat]
          have h_num_bd : ‖z * ((n + 1 : ℕ) : ℂ) ^ 2 - z * (t : ℂ) ^ 2 + Complex.I * t * z ^ 2‖ ≤
              (‖z‖ + ‖z‖ ^ 2 + 1) * (t ^ 2 + (n + 1 : ℝ) ^ 2) := by
            have h1' : ‖z * ((n + 1 : ℕ) : ℂ) ^ 2‖ = ‖z‖ * (n + 1 : ℝ) ^ 2 := by
              rw [norm_mul, norm_pow, Complex.norm_natCast]; push_cast; rfl
            have h2'' : ‖z * (t : ℂ) ^ 2‖ = ‖z‖ * t ^ 2 := by
              rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
            have h3' : ‖Complex.I * t * z ^ 2‖ ≤ ‖z‖ ^ 2 * t ^ 2 := by
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos ht_pos, norm_pow]
              have : t ≤ t ^ 2 := by nlinarith
              nlinarith [sq_nonneg ‖z‖]
            calc ‖z * ((n + 1 : ℕ) : ℂ) ^ 2 - z * (t : ℂ) ^ 2 + Complex.I * t * z ^ 2‖
                ≤ ‖z * ((n + 1 : ℕ) : ℂ) ^ 2‖ + ‖z * (t : ℂ) ^ 2‖ + ‖Complex.I * t * z ^ 2‖ :=
                  (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
              _ ≤ ‖z‖ * (n + 1 : ℝ) ^ 2 + ‖z‖ * t ^ 2 + ‖z‖ ^ 2 * t ^ 2 := by linarith
              _ ≤ (‖z‖ + ‖z‖ ^ 2 + 1) * (t ^ 2 + (n + 1 : ℝ) ^ 2) := by
                  nlinarith [sq_nonneg (n + 1 : ℝ), sq_nonneg t, norm_nonneg z]
          have h_den_lb : (t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 ≤ ‖w t - (n + 1 : ℕ)‖ * ‖w t + (n + 1 : ℕ)‖ := by
            have him_lb : t / 2 ≤ ‖w t - (n + 1 : ℕ)‖ ∧ t / 2 ≤ ‖w t + (n + 1 : ℕ)‖ := by
              have h_im_t : t / 2 ≤ z.im + t := by
                have := neg_le_abs z.im
                have := Complex.abs_im_le_norm z
                linarith
              constructor
              · have := Complex.abs_im_le_norm (w t - (n + 1 : ℕ))
                simp only [w, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
                  Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, add_zero, one_mul,
                  Complex.natCast_im, sub_zero] at this
                linarith [le_abs_self (z.im + t), h_im_t]
              · have := Complex.abs_im_le_norm (w t + (n + 1 : ℕ))
                simp only [w, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                  Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, add_zero, one_mul,
                  Complex.natCast_im] at this
                linarith [le_abs_self (z.im + t), h_im_t]
            by_cases hm : n + 1 ≤ 2 * Nat.ceil |z.re| + 2
            · have hm_le : (n + 1 : ℝ) ≤ 2 * ‖z‖ + 4 := by
                have hceil : (Nat.ceil |z.re| : ℝ) ≤ |z.re| + 1 := (Nat.ceil_lt_add_one (abs_nonneg _)).le
                have hzr : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
                have : (n + 1 : ℝ) ≤ 2 * (Nat.ceil |z.re| : ℝ) + 2 := by exact_mod_cast hm
                linarith
              have hm_le_t : (n + 1 : ℝ) ≤ 2 * t := by linarith
              have hsq : (t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 ≤ (t / 2) ^ 2 := by
                have : (n + 1 : ℝ) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
                linarith
              calc (t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 ≤ (t / 2) * (t / 2) := by nlinarith
                _ ≤ ‖w t - (n + 1 : ℕ)‖ * ‖w t + (n + 1 : ℕ)‖ :=
                    mul_le_mul him_lb.1 him_lb.2 (by positivity) (norm_nonneg _)
            · have hgt : 2 * Nat.ceil |z.re| + 2 < n + 1 := not_le.mp hm
              have hre_ge : (n + 1 : ℝ) / 2 ≤ (n + 1 : ℝ) - |z.re| := by
                have hceil : |z.re| ≤ Nat.ceil |z.re| := Nat.le_ceil _
                have : (2 * Nat.ceil |z.re| + 2 : ℝ) < n + 1 := by exact_mod_cast hgt
                linarith
              have hre_lb1 : (n + 1 : ℝ) / 2 ≤ ‖w t - (n + 1 : ℕ)‖ := by
                have h1' := Complex.abs_re_le_norm (w t - (n + 1 : ℕ))
                simp only [w, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
                  Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
                  sub_zero, add_zero, Complex.natCast_re] at h1'
                have h2'' : (n + 1 : ℝ) - |z.re| ≤ |z.re - (n + 1 : ℝ)| := by
                  rw [abs_sub_comm]; exact le_trans (sub_le_sub_left (le_abs_self _) _) (le_abs_self _)
                push_cast at h1' ⊢; linarith
              have hre_lb2 : (n + 1 : ℝ) / 2 ≤ ‖w t + (n + 1 : ℕ)‖ := by
                have h1' := Complex.abs_re_le_norm (w t + (n + 1 : ℕ))
                simp only [w, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                  Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
                  Complex.natCast_re] at h1'
                have h2'' : (n + 1 : ℝ) - |z.re| ≤ |z.re + (n + 1 : ℝ)| := by
                  have := le_abs_self (z.re + (n + 1 : ℝ))
                  have := neg_le_abs z.re
                  linarith
                push_cast at h1' ⊢; linarith
              have hsq1 : t ^ 2 / 8 + (n + 1 : ℝ) ^ 2 / 8 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := by
                have : (t / 2) ^ 2 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t - (n + 1 : ℕ)), ht_pos]) him_lb.1
                have : ((n + 1 : ℝ) / 2) ^ 2 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t - (n + 1 : ℕ))]) hre_lb1
                linarith
              have hsq2 : t ^ 2 / 8 + (n + 1 : ℝ) ^ 2 / 8 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := by
                have : (t / 2) ^ 2 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t + (n + 1 : ℕ)), ht_pos]) him_lb.2
                have : ((n + 1 : ℝ) / 2) ^ 2 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w t + (n + 1 : ℕ))]) hre_lb2
                linarith
              have hsq1' : (t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 ≤ ‖w t - (n + 1 : ℕ)‖ ^ 2 := by linarith [sq_nonneg t, sq_nonneg (n + 1 : ℝ)]
              have hsq2' : (t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 ≤ ‖w t + (n + 1 : ℕ)‖ ^ 2 := by linarith [sq_nonneg t, sq_nonneg (n + 1 : ℝ)]
              have hprod : ((t ^ 2 + (n + 1 : ℝ) ^ 2) / 20) ^ 2 ≤
                  (‖w t - (n + 1 : ℕ)‖ * ‖w t + (n + 1 : ℕ)‖) ^ 2 := by
                rw [sq, mul_pow]; exact mul_le_mul hsq1' hsq2' (by positivity) (by positivity)
              exact (sq_le_sq₀ (by positivity) (by positivity)).mp hprod
          have h_r_norm : ‖(t ^ 2 + ((n + 1 : ℕ) : ℂ) ^ 2)‖ = t ^ 2 + (n + 1 : ℝ) ^ 2 := by
            have heq : (t : ℂ) ^ 2 + ((n + 1 : ℕ) : ℂ) ^ 2 = ((t ^ 2 + (n + 1 : ℝ) ^ 2 : ℝ) : ℂ) := by
              push_cast; ring
            rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [h_r_norm]
          calc 2 * ‖z * ((n + 1 : ℕ) : ℂ) ^ 2 - z * (t : ℂ) ^ 2 + Complex.I * t * z ^ 2‖ /
                (‖w t - (n + 1 : ℕ)‖ * ‖w t + (n + 1 : ℕ)‖ * (t ^ 2 + (n + 1 : ℝ) ^ 2))
              ≤ 2 * ((‖z‖ + ‖z‖ ^ 2 + 1) * (t ^ 2 + (n + 1 : ℝ) ^ 2)) /
                  ((t ^ 2 + (n + 1 : ℝ) ^ 2) / 20 * (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
                gcongr
            _ = C_z * (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
                dsimp only [C_z]
                field_simp [(by positivity : (0 : ℝ) < t ^ 2 + (n + 1 : ℝ) ^ 2)]
                ring
        have h_tsum_bd : ‖∑' n : ℕ, (f n t - (-Complex.I * ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)))‖ ≤
            ∑' n : ℕ, C_z * (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
          refine (norm_tsum_le_tsum_norm (hs1.sub hs2).norm).trans ?_
          exact Summable.tsum_le_tsum h_term_bd (hs1.sub hs2).norm (hs_r_inv.mul_left C_z)
        have h_pi_bd : ∑' n : ℕ, (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) ≤ Real.pi / (2 * t) := by
          have h_2t := (tsum_two_t_div_sq_bd t (by linarith)).2
          have heq : (∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2)) =
              (2 * t) * ∑' n : ℕ, (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
            rw [← tsum_mul_left]; congr 1; ext n; ring
          rw [heq] at h_2t
          exact (le_div_iff₀' (by positivity)).mpr h_2t
        calc ‖∑' n : ℕ, (f n t - (-Complex.I * ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)))‖
            ≤ C_z * ∑' n : ℕ, (1 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
              rw [← tsum_mul_left]; exact h_tsum_bd
          _ ≤ C_z * (Real.pi / (2 * t)) := by gcongr
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using (tendsto_const_nhds (x := C_z)).mul ((tendsto_const_nhds (x := Real.pi)).div_atTop ((tendsto_id : Tendsto id atTop atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 2))))
        (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
    have h_main_lim : Tendsto (fun t : ℝ =>
        -Complex.I * ∑' n : ℕ, ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ))
        atTop (nhds (-Real.pi * Complex.I)) := by
      have h1 : Tendsto (fun t : ℝ => ∑' n : ℕ, ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ))
          atTop (nhds (Real.pi : ℂ)) := by
        have h_eq : (fun t : ℝ => ∑' n : ℕ, ((2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)) =
            fun t : ℝ => ((∑' n : ℕ, 2 * t / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ) := by
          ext t; rw [Complex.ofReal_tsum]
        rw [h_eq]
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp tsum_two_t_div_sq_tendsto
      have h2 := h1.const_mul (-Complex.I)
      simpa [mul_comm] using h2
    have h_f_lim : Tendsto (fun t : ℝ => ∑' n : ℕ, f n t) atTop (nhds (-Real.pi * Complex.I)) := by
      have := h_diff_lim.add h_main_lim
      simpa using this
    have := h0_lim.add h_f_lim
    simpa using this
  have hg_lim : Tendsto g atTop (nhds 0) := by
    have := h_sum_lim.sub h_cot_lim
    simpa [g] using this
  have hg0 : g 0 = 0 := by
    have h_ev : Tendsto g atTop (nhds (g 0)) :=
      tendsto_const_nhds.congr' (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht; exact (hg_const t ht).symm)
    exact tendsto_nhds_unique h_ev hg_lim
  dsimp only [g, w, f] at hg0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hg0
  exact (sub_eq_zero.mp hg0).symm

lemma pi_div_sin_tsum_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    (Real.pi : ℂ) / Complex.sin (Real.pi * z) =
      ∑' k : ℕ,
        ((1 / (z + (2 * k : ℕ)) - 1 / (z + (2 * k + 1 : ℕ))) +
         (1 / (z - (2 * k + 2 : ℕ)) - 1 / (z - (2 * k + 1 : ℕ)))) := by
  have hz_ne : ∀ m : ℤ, z - m ≠ 0 := fun m h0 => by
    have him := congr_arg Complex.im h0; simp at him; linarith
  have hzh_ne : ∀ m : ℤ, z / 2 - m ≠ 0 := fun m h0 => by
    have him := congr_arg Complex.im h0; simp at him; linarith
  have h_trig : (Real.pi : ℂ) / Complex.sin (Real.pi * z) =
      (Real.pi : ℂ) * Complex.cos (Real.pi * (z / 2)) / Complex.sin (Real.pi * (z / 2)) -
      (Real.pi : ℂ) * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z) := by
    have hsin_z : Complex.sin (Real.pi * z) ≠ 0 := by
      intro h0; rw [Complex.sin_eq_zero_iff] at h0; obtain ⟨m, hm⟩ := h0
      have him := congr_arg Complex.im hm
      have him' : Real.pi * z.im = 0 := by simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
      nlinarith [Real.pi_pos]
    have hsin_h : Complex.sin (Real.pi * (z / 2)) ≠ 0 := by
      intro h0; rw [Complex.sin_eq_zero_iff] at h0; obtain ⟨m, hm⟩ := h0
      have him := congr_arg Complex.im hm
      have him' : Real.pi * (z / 2).im = 0 := by simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
      have : (z / 2).im = z.im / 2 := by simp
      nlinarith [Real.pi_pos]
    have h_dbl : Complex.sin (Real.pi * z) =
        2 * Complex.sin (Real.pi * (z / 2)) * Complex.cos (Real.pi * (z / 2)) := by
      rw [show Real.pi * z = 2 * (Real.pi * (z / 2)) by ring, Complex.sin_two_mul]
    have h_cos_dbl : Complex.cos (Real.pi * z) =
        2 * Complex.cos (Real.pi * (z / 2)) ^ 2 - 1 := by
      rw [show Real.pi * z = 2 * (Real.pi * (z / 2)) by ring, Complex.cos_two_mul]
    have h_pz : Real.pi * (z / 2) = Real.pi * z / 2 := by ring
    rw [h_dbl, h_cos_dbl]
    rw [h_pz] at hsin_h ⊢
    field_simp [hsin_z, hsin_h]
    ring
  let A : ℕ → ℂ := fun n => 1 / (z / 2 - (n + 1 : ℕ)) + 1 / (z / 2 + (n + 1 : ℕ))
  let B : ℕ → ℂ := fun n => 1 / (z - (n + 1 : ℕ)) + 1 / (z + (n + 1 : ℕ))
  let C : ℕ → ℂ := fun k =>
    (1 / (z + (2 * k : ℕ)) - 1 / (z + (2 * k + 1 : ℕ))) +
    (1 / (z - (2 * k + 2 : ℕ)) - 1 / (z - (2 * k + 1 : ℕ)))
  have hA_summ : Summable A := summable_inv_add_inv_complex
    (fun n => by simpa using hzh_ne (n + 1 : ℤ))
    (fun n => by have := hzh_ne (-(n + 1 : ℤ)); push_cast at this ⊢; convert this using 1; ring)
  have hB_summ : Summable B := summable_inv_add_inv_complex
    (fun n => by simpa using hz_ne (n + 1 : ℤ))
    (fun n => by have := hz_ne (-(n + 1 : ℤ)); push_cast at this ⊢; convert this using 1; ring)
  have hC_summ : Summable C := by
    let K : ℕ := Nat.ceil ‖z‖ + 1
    rw [← summable_nat_add_iff K]
    refine (summable_one_div_sq_nat.mul_left 2).of_norm_bounded fun k => ?_
    have h_bd_sub : ∀ m : ℕ, 2 * (k + K) + 1 ≤ m → (k + 1 : ℝ) ≤ ‖z - (m : ℕ)‖ := by
      intro m hm
      have h1 : (m : ℝ) - ‖z‖ ≤ ‖z - (m : ℕ)‖ := by
        have := norm_sub_norm_le ((m : ℕ) : ℂ) z
        rw [norm_sub_rev, Complex.norm_natCast] at this
        linarith
      have h2 : (k + 1 : ℝ) ≤ (m : ℝ) - ‖z‖ := by
        have hm' : (2 * (k + K) + 1 : ℝ) ≤ m := by exact_mod_cast hm
        have hzl : ‖z‖ ≤ (K : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil ‖z‖ ≤ K))
        linarith
      exact h2.trans h1
    have h_bd_add : ∀ m : ℕ, 2 * (k + K) ≤ m → (k + 1 : ℝ) ≤ ‖z + (m : ℕ)‖ := by
      intro m hm
      have h1 : (m : ℝ) - ‖z‖ ≤ ‖z + (m : ℕ)‖ := by
        have := norm_sub_norm_le ((m : ℕ) : ℂ) (-z)
        rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_natCast] at this
        linarith
      have h2 : (k + 1 : ℝ) ≤ (m : ℝ) - ‖z‖ := by
        have hm' : (2 * (k + K) : ℝ) ≤ m := by exact_mod_cast hm
        have hzl : ‖z‖ ≤ (K : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil ‖z‖ ≤ K))
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
        linarith
      exact h2.trans h1
    have h1_eq : 1 / (z + (2 * (k + K) : ℕ)) - 1 / (z + (2 * (k + K) + 1 : ℕ)) =
        1 / ((z + (2 * (k + K) : ℕ)) * (z + (2 * (k + K) + 1 : ℕ))) := by
      have hne1 : z + (2 * (k + K) : ℕ) ≠ 0 := by
        have := hz_ne (-(2 * (k + K) : ℤ)); push_cast at this ⊢; convert this using 1; ring
      have hne2 : z + (2 * (k + K) + 1 : ℕ) ≠ 0 := by
        have := hz_ne (-(2 * (k + K) + 1 : ℤ)); push_cast at this ⊢; convert this using 1; ring
      field_simp [hne1, hne2]; push_cast; ring
    have h2_eq : 1 / (z - (2 * (k + K) + 2 : ℕ)) - 1 / (z - (2 * (k + K) + 1 : ℕ)) =
        1 / ((z - (2 * (k + K) + 2 : ℕ)) * (z - (2 * (k + K) + 1 : ℕ))) := by
      have hne1 : z - (2 * (k + K) + 2 : ℕ) ≠ 0 := by simpa using hz_ne (2 * (k + K) + 2 : ℤ)
      have hne2 : z - (2 * (k + K) + 1 : ℕ) ≠ 0 := by simpa using hz_ne (2 * (k + K) + 1 : ℤ)
      field_simp [hne1, hne2]; push_cast; ring
    have hC_eq : C (k + K) =
        (1 / (z + (2 * (k + K) : ℕ)) - 1 / (z + (2 * (k + K) + 1 : ℕ))) +
        (1 / (z - (2 * (k + K) + 2 : ℕ)) - 1 / (z - (2 * (k + K) + 1 : ℕ))) := by
      dsimp only [C]
    rw [hC_eq, h1_eq, h2_eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_one, norm_mul, norm_div, norm_one, norm_mul]
    have h_p1 : (k + 1 : ℝ) ^ 2 ≤ ‖z + (2 * (k + K) : ℕ)‖ * ‖z + (2 * (k + K) + 1 : ℕ)‖ := by
      rw [sq]; exact mul_le_mul (h_bd_add (2 * (k + K)) le_rfl)
        (h_bd_add (2 * (k + K) + 1) (by omega)) (by positivity) (norm_nonneg _)
    have h_p2 : (k + 1 : ℝ) ^ 2 ≤ ‖z - (2 * (k + K) + 2 : ℕ)‖ * ‖z - (2 * (k + K) + 1 : ℕ)‖ := by
      rw [sq]; exact mul_le_mul (h_bd_sub (2 * (k + K) + 2) (by omega))
        (h_bd_sub (2 * (k + K) + 1) le_rfl) (by positivity) (norm_nonneg _)
    calc 1 / (‖z + (2 * (k + K) : ℕ)‖ * ‖z + (2 * (k + K) + 1 : ℕ)‖) +
          1 / (‖z - (2 * (k + K) + 2 : ℕ)‖ * ‖z - (2 * (k + K) + 1 : ℕ)‖)
        ≤ 1 / (k + 1 : ℝ) ^ 2 + 1 / (k + 1 : ℝ) ^ 2 := by gcongr
      _ = 2 * ((1 : ℝ) / (k + 1 : ℝ) ^ 2) := by ring
  have h_id : ∀ N : ℕ,
      (1 / (z / 2) + ∑ n ∈ Finset.range N, A n) -
        (1 / z + ∑ n ∈ Finset.range (2 * N), B n) =
      (∑ k ∈ Finset.range N, C k) + 1 / (z + (2 * N : ℕ)) := by
    intro N
    induction N with
    | zero => simp; ring
    | succ N ih =>
      rw [Finset.sum_range_succ, show 2 * (N + 1) = 2 * N + 2 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ C]
      have hA_eq : A N = (1 / (z - (2 * N + 2 : ℕ)) + 1 / (z + (2 * N + 2 : ℕ))) * 2 := by
        dsimp only [A]; push_cast; field_simp
      have hB0 : B (2 * N) = 1 / (z - (2 * N + 1 : ℕ)) + 1 / (z + (2 * N + 1 : ℕ)) := by
        dsimp only [B]
      have hB1 : B (2 * N + 1) = 1 / (z - (2 * N + 2 : ℕ)) + 1 / (z + (2 * N + 2 : ℕ)) := by
        dsimp only [B]
      have hC_eq : C N = (1 / (z + (2 * N : ℕ)) - 1 / (z + (2 * N + 1 : ℕ))) +
          (1 / (z - (2 * N + 2 : ℕ)) - 1 / (z - (2 * N + 1 : ℕ))) := by
        dsimp only [C]
      have h_lhs_step :
          (1 / (z / 2) + (∑ n ∈ Finset.range N, A n + A N)) -
            (1 / z + (∑ n ∈ Finset.range (2 * N), B n + B (2 * N) + B (2 * N + 1))) =
          ((1 / (z / 2) + ∑ n ∈ Finset.range N, A n) - (1 / z + ∑ n ∈ Finset.range (2 * N), B n)) +
            (A N - B (2 * N) - B (2 * N + 1)) := by ring
      rw [h_lhs_step, ih, hA_eq, hB0, hB1, hC_eq]
      push_cast; ring
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
  have h_lim_lhs : Tendsto (fun N : ℕ =>
      (1 / (z / 2) + ∑ n ∈ Finset.range N, A n) - (1 / z + ∑ n ∈ Finset.range (2 * N), B n))
      atTop (nhds ((1 / (z / 2) + ∑' n : ℕ, A n) - (1 / z + ∑' n : ℕ, B n))) :=
    (tendsto_const_nhds.add hA_summ.hasSum.tendsto_sum_nat).sub
      (tendsto_const_nhds.add (hB_summ.hasSum.tendsto_sum_nat.comp h2N))
  have h_tail_lim : Tendsto (fun N : ℕ => (1 : ℂ) / (z + (2 * N : ℕ))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bnd : ∀ᶠ N : ℕ in atTop, ‖(1 : ℂ) / (z + (2 * N : ℕ))‖ ≤ 1 / (N + 1 : ℝ) := by
      filter_upwards [eventually_ge_atTop (Nat.ceil ‖z‖ + 1)] with N hN
      rw [norm_div, norm_one]
      have h1 : (N + 1 : ℝ) ≤ ‖z + (2 * N : ℕ)‖ := by
        have h_sub := norm_sub_norm_le ((2 * N : ℕ) : ℂ) (-z)
        rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_natCast] at h_sub
        have : (Nat.ceil ‖z‖ + 1 : ℝ) ≤ N := by exact_mod_cast hN
        have : ‖z‖ ≤ Nat.ceil ‖z‖ := Nat.le_ceil _
        push_cast at h_sub ⊢; linarith
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
  have h_lim_rhs : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, C k) + 1 / (z + (2 * N : ℕ)))
      atTop (nhds ((∑' k : ℕ, C k) + 0)) :=
    hC_summ.hasSum.tendsto_sum_nat.add h_tail_lim
  simp_rw [← h_id] at h_lim_rhs
  have h_eq_lim := tendsto_nhds_unique h_lim_lhs h_lim_rhs
  rw [add_zero] at h_eq_lim
  rw [h_trig, pi_cot_tsum_eq (by simpa using half_pos hz), pi_cot_tsum_eq hz]
  exact h_eq_lim

lemma pi_div_cos_tsum_eq {θ x : ℝ} (hθ : |θ| < Real.pi / 2) (hx : x ≠ 0) :
    (Real.pi : ℂ) / Complex.cos (θ + Complex.I * x / 2) =
      ∑' k : ℕ,
        ((2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x) -
          2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ + Complex.I * x)) +
         (2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ - Complex.I * x) -
          2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi - 2 * θ - Complex.I * x))) := by
  have h_for_neg : ∀ (θ' x' : ℝ), |θ'| < Real.pi / 2 → x' < 0 →
      (Real.pi : ℂ) / Complex.cos (θ' + Complex.I * x' / 2) =
        ∑' k : ℕ,
          ((2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x') -
            2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x')) +
           (2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ' - Complex.I * x') -
            2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi - 2 * θ' - Complex.I * x'))) := by
    intro θ' x' _ hx'
    let z : ℂ := 1 / 2 - (θ' + Complex.I * x' / 2) / Real.pi
    have hz : 0 < z.im := by
      dsimp only [z]
      rw [Complex.sub_im, Complex.div_ofReal_im]
      have h1 : ((1 : ℂ) / 2).im = 0 := by norm_num
      have h2 : (θ' + Complex.I * x' / 2).im = x' / 2 := by
        rw [Complex.add_im, Complex.ofReal_im, zero_add]
        rw [show Complex.I * (x' : ℂ) / 2 = ((x' / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [h1, h2]
      have : x' / 2 / Real.pi < 0 := div_neg_of_neg_of_pos (by linarith) Real.pi_pos
      linarith
    have hsin_eq : Complex.sin (Real.pi * z) = Complex.cos (θ' + Complex.I * x' / 2) := by
      have hpz : Real.pi * z = Real.pi / 2 - (θ' + Complex.I * x' / 2) := by
        dsimp only [z]; field_simp [Real.pi_ne_zero]
      rw [hpz, Complex.sin_pi_div_two_sub]
    rw [← hsin_eq, pi_div_sin_tsum_of_im_pos hz]
    congr 1; ext k
    have h1 : 1 / (z + (2 * k : ℕ)) =
        2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi - 2 * θ' - Complex.I * x') := by
      dsimp only [z]; push_cast; field_simp [Real.pi_ne_zero]; ring
    have h2 : 1 / (z + (2 * k + 1 : ℕ)) =
        2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi - 2 * θ' - Complex.I * x') := by
      dsimp only [z]; push_cast; field_simp [Real.pi_ne_zero]; ring
    have h3 : 1 / (z - (2 * k + 2 : ℕ)) =
        -2 * Real.pi / (((4 * k + 3 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x') := by
      dsimp only [z]; push_cast; field_simp [Real.pi_ne_zero]
      rw [← div_neg]; congr 1; ring
    have h4 : 1 / (z - (2 * k + 1 : ℕ)) =
        -2 * Real.pi / (((4 * k + 1 : ℕ) : ℝ) * Real.pi + 2 * θ' + Complex.I * x') := by
      dsimp only [z]; push_cast; field_simp [Real.pi_ne_zero]
      rw [← div_neg]; congr 1; ring
    rw [h1, h2, h3, h4]
    ring
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · exact h_for_neg θ x hθ hx_neg
  · have hcos_neg : Complex.cos (θ + Complex.I * x / 2) = Complex.cos ((-θ) + Complex.I * (-x) / 2) := by
      rw [← Complex.cos_neg]; congr 1; push_cast; ring
    rw [hcos_neg]
    rw [show (-θ : ℂ) + Complex.I * (-x : ℂ) / 2 = ((-θ : ℝ) : ℂ) + Complex.I * ((-x : ℝ) : ℂ) / 2 by push_cast; ring]
    rw [h_for_neg (-θ) (-x) (by rwa [abs_neg]) (by linarith)]
    congr 1; ext k; push_cast; ring


end PolarEvaluation
