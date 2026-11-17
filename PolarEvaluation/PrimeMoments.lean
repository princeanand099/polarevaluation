import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.PrimeMomentsCore

/-!
# High-Moment Estimates for Prime Sums (Section 6 & Lemma 4.2)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

lemma prime_tuple_fiber_card (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (k n : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => S)).filter (fun f => (∏ i, f i) = n)).card ≤ k.factorial := by
  induction k generalizing n with
  | zero =>
    have hsub : Subsingleton (Fin 0 → ℕ) := inferInstance
    exact (Finset.card_le_one_of_subsingleton _).trans (by simp)
  | succ k ih =>
    set F := (Fintype.piFinset (fun _ : Fin (k + 1) => S)).filter (fun f => (∏ i, f i) = n)
    by_cases h_emp : F = ∅
    · rw [h_emp, Finset.card_empty]; exact Nat.zero_le _
    · obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_emp
      simp only [F, Finset.mem_filter, Fintype.mem_piFinset] at hf₀
      have hn_pos : 0 < n := by
        rw [← hf₀.2]
        exact Finset.prod_pos (fun i _ => (hS _ (hf₀.1 i)).pos)
      have hpf_sub : n.primeFactors ⊆ Finset.image f₀ Finset.univ := by
        intro p hp
        have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hp_dvd_n : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hp_dvd : p ∣ ∏ i : Fin (k + 1), f₀ i := by rw [hf₀.2]; exact hp_dvd_n
        obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hp_prime).dvd_finset_prod_iff (fun i => f₀ i)).mp hp_dvd
        have hpeq : p = f₀ i := (Nat.prime_dvd_prime_iff_eq hp_prime (hS _ (hf₀.1 i))).mp hi
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hpeq.symm⟩
      have hpf_card : n.primeFactors.card ≤ k + 1 :=
        (Finset.card_le_card hpf_sub).trans (Finset.card_image_le.trans (by simp))
      have hF_sub : F ⊆ n.primeFactors.biUnion (fun p => F.filter (fun f => f 0 = p)) := by
        intro f hf
        simp only [F, Finset.mem_filter, Fintype.mem_piFinset] at hf
        refine Finset.mem_biUnion.mpr ⟨f 0, ?_,
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hf.1, hf.2⟩, rfl⟩⟩
        rw [Nat.mem_primeFactors]
        refine ⟨hS _ (hf.1 0), ?_, hn_pos.ne'⟩
        rw [← hf.2]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ 0)
      have h_fiber : ∀ p ∈ n.primeFactors, (F.filter (fun f => f 0 = p)).card ≤ k.factorial := by
        intro p hp
        set G := (Fintype.piFinset (fun _ : Fin k => S)).filter (fun g => (∏ i, g i) = n / p)
        have h_card_le : (F.filter (fun f => f 0 = p)).card ≤ G.card := by
          refine Finset.card_le_card_of_injOn (fun f i => f i.succ) ?_ ?_
          · intro f hf
            rw [Finset.mem_coe, Finset.mem_filter] at hf
            rw [Finset.mem_coe]
            dsimp only [G]
            rw [Finset.mem_filter, Fintype.mem_piFinset]
            have hf1 : ∀ i, f i ∈ S := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf.1).1
            have hf2 : (∏ i, f i) = n := (Finset.mem_filter.mp hf.1).2
            refine ⟨fun i => hf1 i.succ, ?_⟩
            have hprod : p * ∏ i : Fin k, f i.succ = n := by
              rw [← hf2, Fin.prod_univ_succ, hf.2]
            have hp_pos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
            dsimp only; exact Nat.eq_div_of_mul_eq_right hp_pos.ne' hprod
          · intro f₁ hf₁ f₂ hf₂ heq
            rw [Finset.mem_coe, Finset.mem_filter] at hf₁ hf₂
            funext i
            refine Fin.cases ?_ (fun j => congr_fun heq j) i
            exact hf₁.2.trans hf₂.2.symm
        exact h_card_le.trans (ih (n / p))
      calc F.card ≤ (n.primeFactors.biUnion (fun p => F.filter (fun f => f 0 = p))).card :=
            Finset.card_le_card hF_sub
        _ ≤ ∑ p ∈ n.primeFactors, (F.filter (fun f => f 0 = p)).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ n.primeFactors, k.factorial := Finset.sum_le_sum h_fiber
        _ = n.primeFactors.card * k.factorial := by simp
        _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_right _ hpf_card
        _ = (k + 1).factorial := (Nat.factorial_succ k).symm

lemma factorial_le_pow (k : ℕ) : k.factorial ≤ k ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    refine Nat.mul_le_mul_left (k + 1) (ih.trans (Nat.pow_le_pow_left (by omega) k))

lemma prime_l2_sum_bound (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_l2 > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∑ p ∈ (Finset.Icc 2 (Nat.floor (Real.exp (2 * Real.pi * Δ)))).filter Nat.Prime,
        ((Real.log p / Real.sqrt p) *
          max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
              ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖) ^ 2 ≤
        C_l2 * Real.log (Real.log (Real.exp (2 * Real.pi * Δ))) := by
  obtain ⟨C_dec, hC_dec, h_dec⟩ := majorant_fourier_decay_any θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨400 * C_dec ^ 2, by positivity, fun Δ M hΔ hInt hL1 => ?_⟩
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  have hΔ_ge1 : 1 ≤ Δ := hΔ₀.trans hΔ
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hloglogX_ge : 1 ≤ Real.log (Real.log X) := by
    rw [hlogX_eq]
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by nlinarith [Real.two_le_pi])
  have hX_ge_16 : (16 : ℝ) ≤ X := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h4 : (4 : ℝ) ≤ 2 * Real.pi * Δ := by nlinarith [Real.two_le_pi]
    calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ X := Real.exp_le_exp.mpr h4
  have hP_ge_3 : P ≥ 3 := Nat.le_floor (by norm_num; linarith)
  have hP_le_X : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
  have h_term : ∀ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
      ((Real.log p / Real.sqrt p) *
        max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
            ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖) ^ 2 ≤
      2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.2.one_lt)
    have hξ_pos : 0 < Real.log p / (2 * Real.pi) := by positivity
    have h_abs_eq : 1 / (2 * Real.pi * |Real.log p / (2 * Real.pi)|) = 1 / Real.log p := by
      rw [abs_of_pos hξ_pos]
      field_simp [Real.pi_ne_zero]
    have h_nabs_eq : 1 / (2 * Real.pi * |-(Real.log p / (2 * Real.pi))|) = 1 / Real.log p := by
      rw [abs_neg]; exact h_abs_eq
    have hs_bd : max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.log p + 1 / Δ) := by
      refine max_le ?_ ?_
      · have hd := h_dec Δ M hΔ hInt hL1 (-(Real.log p / (2 * Real.pi))) (neg_ne_zero.mpr hξ_pos.ne')
        rwa [h_nabs_eq] at hd
      · have hd := h_dec Δ M hΔ hInt hL1 (Real.log p / (2 * Real.pi)) hξ_pos.ne'
        rwa [h_abs_eq] at hd
    have h_prod_bd : (Real.log p / Real.sqrt p) *
        max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
            ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) := by
      calc (Real.log p / Real.sqrt p) * max _ _
          ≤ (Real.log p / Real.sqrt p) * (C_dec * (1 / Real.log p + 1 / Δ)) := by gcongr
        _ = C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) := by
            field_simp [hlogp_pos.ne', (Real.sqrt_pos.mpr hp_pos).ne', (by linarith : Δ ≠ 0)]
    have h_sq_le : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := fun a b => by
      nlinarith [sq_nonneg (a - b)]
    calc ((Real.log p / Real.sqrt p) * max _ _) ^ 2
        ≤ (C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p))) ^ 2 := by
          gcongr
      _ = C_dec ^ 2 * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) ^ 2 := by ring
      _ ≤ C_dec ^ 2 * (2 * ((1 / Real.sqrt p) ^ 2 + (Real.log p / (Δ * Real.sqrt p)) ^ 2)) := by
          gcongr; exact h_sq_le _ _
      _ = 2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
          rw [div_pow, one_pow, div_pow, mul_pow, Real.sq_sqrt hp_pos.le]
          ring
  have hm2 : ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (1 : ℝ) / p ≤ 30 * Real.log (Real.log X) := by
    have h1 := mertens_second P hP_ge_3
    have hloglog : Real.log (Real.log P) ≤ Real.log (Real.log X) :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < P)))
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < P)) hP_le_X)
    nlinarith
  have hm1 : ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p) ≤
      170 * Real.log (Real.log X) := by
    have hlogP_le : Real.log P ≤ 2 * Real.pi * Δ := by
      rw [← hlogX_eq]
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < P)) hP_le_X
    have hterm1 : ∀ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        (Real.log p) ^ 2 / (Δ ^ 2 * p) ≤ (2 * Real.pi / Δ) * (Real.log p / p) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      have hlogp_le : Real.log p ≤ 2 * Real.pi * Δ :=
        (Real.log_le_log hp_pos (by exact_mod_cast hp.1.2)).trans hlogP_le
      have hlogp_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
      have heq1 : (Real.log p) ^ 2 / (Δ ^ 2 * p) = (Real.log p / Δ ^ 2) * (Real.log p / p) := by ring
      have heq2 : Real.log p / Δ ^ 2 ≤ 2 * Real.pi / Δ := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [Real.pi_pos]
      rw [heq1]
      exact mul_le_mul_of_nonneg_right heq2 (div_nonneg hlogp_nonneg hp_pos.le)
    have hmf := mertens_first P (by omega)
    have hlog4_le : Real.log 4 ≤ 2 := by
      have hlog2_le : Real.log 2 ≤ 1 := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) he
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; linarith
    calc ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p)
        ≤ ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (2 * Real.pi / Δ) * (Real.log p / p) :=
          Finset.sum_le_sum hterm1
      _ = (2 * Real.pi / Δ) * ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, Real.log p / p := by
          rw [← Finset.mul_sum]
      _ ≤ (2 * Real.pi / Δ) * (Real.log 4 * (Real.log P + 1)) := by gcongr
      _ ≤ (2 * Real.pi / Δ) * (2 * (2 * Real.pi * Δ + 1)) := by gcongr
      _ = 8 * Real.pi ^ 2 + 4 * Real.pi / Δ := by field_simp [(by linarith : Δ ≠ 0)]; ring
      _ ≤ 8 * 4 ^ 2 + 4 * 4 / 1 := by
          have hpi := Real.pi_lt_four
          gcongr
      _ = 144 := by norm_num
      _ ≤ 170 * Real.log (Real.log X) := by nlinarith [hloglogX_ge]
  calc ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ((Real.log p / Real.sqrt p) * max _ _) ^ 2
      ≤ ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
          2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) :=
        Finset.sum_le_sum h_term
    _ = 2 * C_dec ^ 2 * (∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (1 : ℝ) / p +
          ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * C_dec ^ 2 * (30 * Real.log (Real.log X) + 170 * Real.log (Real.log X)) := by
        gcongr
    _ = 400 * C_dec ^ 2 * Real.log (Real.log X) := by ring

/-- **Lemma 4.2(i)** (`2k`-th moment bound in the `t`-aspect). -/
theorem prime_moment_t_aspect (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ B > 0, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Δ T : ℝ) (k : ℕ) (M : ℝ → ℝ),
      q ≥ 1 → Δ ≥ Δ₀ → T ≥ 10 →
      (Real.exp (2 * Real.pi * Δ)) ^ k ≤ T →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1 →
      (1 / T) * ∫ t in Set.Icc T (2 * T),
        |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) (Real.exp (2 * Real.pi * Δ)) t| ^ (2 * k) ≤
        (B * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  obtain ⟨C₂, hC₂, hmvt⟩ := montgomery_vaughan_mvt
  obtain ⟨C_l2, hC_l2, hl2⟩ := prime_l2_sum_bound θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨max (8 * max C₂ 1 * C_l2) 1, by positivity,
    fun q χ Δ T k M hq hΔ hT hXk hInt hL1 hL1_M => ?_⟩
  set B := max (8 * max C₂ 1 * C_l2) 1
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  set h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [mul_zero, pow_zero, Nat.cast_zero]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
    have : 2 * T - T = T := by ring
    rw [this, one_div_mul_cancel (by linarith)]
  · let primes := (Finset.Icc 2 P).filter Nat.Prime
    let b₁ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * χ p * h_hat (-(Real.log p / (2 * Real.pi)))
    let b₂ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * χ p * star (h_hat (Real.log p / (2 * Real.pi)))
    let D₁ : ℝ → ℂ := fun t => ∑ p ∈ primes, b₁ p * Complex.exp (-Complex.I * t * Real.log p)
    let D₂ : ℝ → ℂ := fun t => ∑ p ∈ primes, b₂ p * Complex.exp (-Complex.I * t * Real.log p)
    have h_ptwise : ∀ t : ℝ,
        |primeSum1 q χ h_hat X t| ^ (2 * k) ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
      intro t
      have h_le : |primeSum1 q χ h_hat X t| ≤ ‖D₁ t‖ + ‖D₂ t‖ := by
        unfold primeSum1
        have h_sum_eq : (∑ p ∈ primes, (Real.log p / Real.sqrt p) *
            (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log p) +
             star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log p)).re) =
            (D₁ t).re + (star (D₂ t)).re := by
          simp only [D₁, D₂, b₁, b₂, Complex.re_sum, star_sum, Complex.star_def, star_mul,
            Complex.conj_ofReal]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hce : (starRingEnd ℂ) (Complex.exp (-Complex.I * ↑t * ↑(Real.log p))) =
              Complex.exp (Complex.I * ↑t * ↑(Real.log p)) := by
            rw [← Complex.exp_conj]
            congr 1
            simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
            ring
          rw [hce]
          have hstar2 : (starRingEnd ℂ) ((starRingEnd ℂ) (h_hat (Real.log ↑p / (2 * Real.pi)))) =
              h_hat (Real.log ↑p / (2 * Real.pi)) := star_star _
          rw [hstar2, ← Complex.add_re, ← Complex.re_ofReal_mul]
          congr 1
          ring
        rw [h_sum_eq]
        have h2pi_le : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
        calc (1 / (2 * Real.pi)) * |(D₁ t).re + (star (D₂ t)).re|
            ≤ 1 * (|(D₁ t).re| + |(star (D₂ t)).re|) := by
              gcongr; exact abs_add_le _ _
          _ ≤ ‖D₁ t‖ + ‖star (D₂ t)‖ := by
              rw [one_mul]
              exact add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          _ = ‖D₁ t‖ + ‖D₂ t‖ := by rw [norm_star]
      have h_max : (‖D₁ t‖ + ‖D₂ t‖) ^ (2 * k) ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
        set m := max ‖D₁ t‖ ‖D₂ t‖
        calc (‖D₁ t‖ + ‖D₂ t‖) ^ (2 * k)
            ≤ (2 * m) ^ (2 * k) := by
              gcongr; linarith [le_max_left ‖D₁ t‖ ‖D₂ t‖, le_max_right ‖D₁ t‖ ‖D₂ t‖]
          _ = 4 ^ k * m ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
              gcongr
              rcases le_total ‖D₁ t‖ ‖D₂ t‖ with h | h
              · simp only [m, max_eq_right h]; linarith [pow_nonneg (norm_nonneg (D₁ t)) (2 * k)]
              · simp only [m, max_eq_left h]; linarith [pow_nonneg (norm_nonneg (D₂ t)) (2 * k)]
      exact (pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)).trans h_max
    have h_poly_bound : ∀ (b : ℕ → ℂ),
        (∀ p ∈ primes, ‖b p‖ ≤ (Real.log p / Real.sqrt p) *
          max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) →
        (1 / T) * ∫ t in Set.Icc T (2 * T),
          ‖∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)‖ ^ (2 * k) ≤
        (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
      intro b hb
      set D : ℝ → ℂ := fun t => ∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)
      let fiber : ℕ → Finset (Fin k → ℕ) := fun n =>
        (Fintype.piFinset (fun _ : Fin k => primes)).filter (fun f => (∏ i, f i) = n)
      let a : ℕ → ℂ := fun n => ∑ f ∈ fiber n, ∏ i, b (f i)
      have h_pow_eq : ∀ t : ℝ, (D t) ^ k = ∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n) := by
        intro t
        dsimp only [D]
        rw [Finset.sum_pow']
        have h_maps : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primes),
            (∏ i : Fin k, f i) ∈ Finset.Icc 1 (P ^ k) := by
          intro f hf
          rw [Fintype.mem_piFinset] at hf
          rw [Finset.mem_Icc]
          refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => ?_)), ?_⟩
          · have hp := hf i
            simp only [primes, Finset.mem_filter] at hp
            exact hp.2.pos
          · calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P := by
                  refine Finset.prod_le_prod' fun i _ => ?_
                  have hp := hf i
                  simp only [primes, Finset.mem_filter, Finset.mem_Icc] at hp
                  exact hp.1.2
              _ = P ^ k := by simp
        rw [← Finset.sum_fiberwise_of_maps_to h_maps]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [a, fiber]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
        rw [Finset.prod_mul_distrib]
        congr 1
        have hpos : ∀ i : Fin k, (0 : ℝ) < f i := fun i => by
          have hp := hf.1 i
          simp only [primes, Finset.mem_filter] at hp
          exact_mod_cast hp.2.pos
        have hexp : ∏ i : Fin k, Complex.exp (-Complex.I * t * Real.log (f i)) =
            Complex.exp (∑ i : Fin k, (-Complex.I * t * Real.log (f i))) := by
          rw [← Complex.exp_sum]
        rw [hexp]
        congr 1
        rw [← hf.2, Nat.cast_prod, Real.log_prod (fun i _ => (hpos i).ne')]
        push_cast
        rw [Finset.mul_sum]
      have h_norm_eq : ∀ t : ℝ, ‖∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)‖ ^ (2 * k) =
          ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n)‖ ^ 2 := by
        intro t
        rw [mul_comm 2 k, pow_mul, ← norm_pow]
        change ‖(D t) ^ k‖ ^ 2 = _
        rw [h_pow_eq t]
      simp_rw [h_norm_eq]
      have hPk_le_T : ((P ^ k : ℕ) : ℝ) ≤ T := by
        have hP_le : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
        calc ((P ^ k : ℕ) : ℝ) = (P : ℝ) ^ k := by push_cast; rfl
          _ ≤ X ^ k := pow_le_pow_left₀ (Nat.cast_nonneg P) hP_le k
          _ ≤ T := hXk
      have hmvt_bd := hmvt (P ^ k) a T (by linarith) hPk_le_T
      have h_cs : ∀ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤ (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
        intro n _
        dsimp only [a]
        have h1 : ‖∑ f ∈ fiber n, ∏ i, b (f i)‖ ^ 2 ≤ (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
        have h2 : (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 ≤ (fiber n).card * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have h_card : (fiber n).card ≤ k.factorial :=
          prime_tuple_fiber_card primes (fun p hp => (Finset.mem_filter.mp hp).2) k n
        have h3 : ((fiber n).card : ℝ) * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 ≤
            (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
          have h_eq : ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 = ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [norm_prod, Finset.prod_pow]
          rw [h_eq]
          gcongr
        exact h1.trans (h2.trans h3)
      have h_sum_a : ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤
          (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
        calc ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2
            ≤ ∑ n ∈ Finset.Icc 1 (P ^ k), (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 :=
              Finset.sum_le_sum h_cs
          _ = (k.factorial : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
              rw [← Finset.mul_sum]
          _ = (k.factorial : ℝ) * ∑ f ∈ Fintype.piFinset (fun _ : Fin k => primes), ∏ i, ‖b (f i)‖ ^ 2 := by
              congr 1
              refine Finset.sum_fiberwise_of_maps_to (fun f hf => ?_) _
              rw [Fintype.mem_piFinset] at hf
              rw [Finset.mem_Icc]
              refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
              calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                    Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
                _ = P ^ k := by simp
          _ = (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
              rw [Finset.sum_pow']
      have h_l2_b : ∑ p ∈ primes, ‖b p‖ ^ 2 ≤ C_l2 * Real.log (Real.log X) := by
        calc ∑ p ∈ primes, ‖b p‖ ^ 2
            ≤ ∑ p ∈ primes, ((Real.log p / Real.sqrt p) *
                max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) ^ 2 := by
              refine Finset.sum_le_sum fun p hp => ?_
              exact pow_le_pow_left₀ (norm_nonneg _) (hb p hp) 2
          _ ≤ C_l2 * Real.log (Real.log X) := hl2 Δ M hΔ hInt hL1
      have h_fac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast factorial_le_pow k
      calc (1 / T) * ∫ t in Set.Icc T (2 * T),
            ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n)‖ ^ 2
          ≤ (1 / T) * (C₂ * T * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2) := by
            gcongr
        _ = C₂ * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := by
            field_simp [(by linarith : T ≠ 0)]
        _ ≤ max C₂ 1 * ((k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k) := by
            gcongr
            exact le_max_left _ _
        _ ≤ max C₂ 1 * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ ≤ (max C₂ 1) ^ k * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            have hloglogX_nonneg : 0 ≤ Real.log (Real.log X) := by
              rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
              apply Real.log_nonneg
              have : 1 ≤ Δ := hΔ₀.trans hΔ
              nlinarith [Real.two_le_pi]
            gcongr
            exact le_self_pow₀ (le_max_right C₂ 1) hk_pos.ne'
        _ = (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
            rw [← mul_pow, ← mul_pow]; ring_nf
    have hchi_le : ∀ p : ℕ, ‖χ p‖ ≤ 1 := fun p => by
      by_cases h0 : χ p = 0
      · simp [h0]
      · exact (dirichletChar_norm_eq_one χ h0).le
    have hb₁ : ∀ p ∈ primes, ‖b₁ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₁]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      calc (Real.log p / Real.sqrt p) * ‖χ p‖ * ‖h_hat (-(Real.log p / (2 * Real.pi)))‖
          ≤ (Real.log p / Real.sqrt p) * 1 *
              max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
            gcongr
            · exact hchi_le p
            · exact le_max_left _ _
        _ = (Real.log p / Real.sqrt p) *
              max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by ring
    have hb₂ : ∀ p ∈ primes, ‖b₂ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₂]
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      calc (Real.log p / Real.sqrt p) * ‖χ p‖ * ‖h_hat (Real.log p / (2 * Real.pi))‖
          ≤ (Real.log p / Real.sqrt p) * 1 *
              max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
            gcongr
            · exact hchi_le p
            · exact le_max_right _ _
        _ = (Real.log p / Real.sqrt p) *
              max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by ring
    have hD₁_int : IntegrableOn (fun t : ℝ => ‖D₁ t‖ ^ (2 * k)) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hD₂_int : IntegrableOn (fun t : ℝ => ‖D₂ t‖ ^ (2 * k)) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hRHS_int : IntegrableOn (fun t : ℝ => 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k))) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hP_int : IntegrableOn (fun t : ℝ => |primeSum1 q χ h_hat X t| ^ (2 * k)) (Set.Icc T (2 * T)) := by
      refine hRHS_int.mono' ?_ ?_
      · exact (Continuous.continuousOn (by unfold primeSum1; fun_prop)).aestronglyMeasurable measurableSet_Icc
      · filter_upwards with t
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact h_ptwise t
    have hloglogX_ge : 0 ≤ Real.log (Real.log X) := by
      rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
      apply Real.log_nonneg
      have : 1 ≤ Δ := hΔ₀.trans hΔ
      nlinarith [Real.two_le_pi]
    calc (1 / T) * ∫ t in Set.Icc T (2 * T), |primeSum1 q χ h_hat X t| ^ (2 * k)
        ≤ (1 / T) * ∫ t in Set.Icc T (2 * T), 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left
            (setIntegral_mono_on hP_int hRHS_int measurableSet_Icc (fun t _ => h_ptwise t))
            (by positivity)
      _ = 4 ^ k * ((1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) +
            (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k))) := by
          have hint_add : ∫ t in Set.Icc T (2 * T), (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) =
              (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) +
              (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k)) :=
            MeasureTheory.integral_add hD₁_int hD₂_int
          rw [MeasureTheory.integral_const_mul, hint_add]
          ring
      _ ≤ 4 ^ k * ((max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k +
            (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k) := by
          have hb1_bd := h_poly_bound b₁ hb₁
          have hb2_bd := h_poly_bound b₂ hb₂
          change (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) ≤ _ at hb1_bd
          change (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k)) ≤ _ at hb2_bd
          exact mul_le_mul_of_nonneg_left (add_le_add hb1_bd hb2_bd) (by positivity)
      _ ≤ 4 ^ k * (2 ^ k * (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k) := by
          have h2k : (2 : ℝ) ≤ 2 ^ k := by
            have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
            simpa using this
          have hnn : 0 ≤ (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_right h2k hnn]) (by positivity)
      _ = (8 * max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
          rw [← mul_pow, ← mul_pow]; ring_nf
      _ ≤ (B * k * Real.log (Real.log X)) ^ k := by
          gcongr
          exact le_max_left _ _

/-- **Lemma 4.2(ii)** (`2k`-th moment bound in the `q`-aspect). -/
theorem prime_moment_q_aspect (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ B > 0, ∀ (q : ℕ) (t₀ Δ : ℝ) (k : ℕ) (M : ℝ → ℝ),
      q ≥ 3 → totientStar q ≥ 1 → Δ ≥ Δ₀ →
      (Real.exp (2 * Real.pi * Δ)) ^ k < (q : ℝ) →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1 →
      letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
      (1 / (totientStar q : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) (Real.exp (2 * Real.pi * Δ)) t₀| ^ (2 * k) ≤
        ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
          (B * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  obtain ⟨C_l2, hC_l2, hl2⟩ := prime_l2_sum_bound θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨max (8 * C_l2) 1, by positivity,
    fun q t₀ Δ k M hq hqstar hΔ hXk hInt hL1 hL1_M => ?_⟩
  classical
  set B := max (8 * C_l2) 1
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  set h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
  have hq_pos : 0 < q := by omega
  have hq_ne : q ≠ 0 := hq_pos.ne'
  haveI : NeZero q := ⟨hq_ne⟩
  have hqstar_pos : (0 : ℝ) < totientStar q := by exact_mod_cast hqstar
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [mul_zero, pow_zero, Nat.cast_zero, mul_one, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card ≤
        Nat.totient q := by
      calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_filter_le _ _
        _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
        _ = Nat.totient q := by rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have h1 : (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card : ℝ) ≤
        (Nat.totient q : ℝ) / (totientStar q : ℝ) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hqstar_pos.le
    simpa [totientStar] using h1
  · let primes := (Finset.Icc 2 P).filter Nat.Prime
    let b₁ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * h_hat (-(Real.log p / (2 * Real.pi))) *
        Complex.exp (-Complex.I * t₀ * Real.log p)
    let b₂ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * star (h_hat (Real.log p / (2 * Real.pi))) *
        Complex.exp (-Complex.I * t₀ * Real.log p)
    let D₁ : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b₁ p * χ p
    let D₂ : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b₂ p * χ p
    have h_ptwise : ∀ χ : DirichletCharacter ℂ q,
        |primeSum1 q χ h_hat X t₀| ^ (2 * k) ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
      intro χ
      have h_le : |primeSum1 q χ h_hat X t₀| ≤ ‖D₁ χ‖ + ‖D₂ χ‖ := by
        unfold primeSum1
        have h_sum_eq : (∑ p ∈ primes, (Real.log p / Real.sqrt p) *
            (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t₀ * Real.log p) +
             star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t₀ * Real.log p)).re) =
            (D₁ χ).re + (star (D₂ χ)).re := by
          simp only [D₁, D₂, b₁, b₂, Complex.re_sum, star_sum, Complex.star_def, star_mul,
            Complex.conj_ofReal]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hce : (starRingEnd ℂ) (Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p))) =
              Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p)) := by
            rw [← Complex.exp_conj]
            congr 1
            simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
            ring
          rw [hce]
          have hstar2 : (starRingEnd ℂ) ((starRingEnd ℂ) (h_hat (Real.log ↑p / (2 * Real.pi)))) =
              h_hat (Real.log ↑p / (2 * Real.pi)) := star_star _
          rw [hstar2, ← Complex.add_re]
          have h_rhs_eq : ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ) * h_hat (-(Real.log ↑p / (2 * Real.pi))) *
              Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p)) * χ ↑p +
              (starRingEnd ℂ) (χ ↑p) * (Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p)) *
                (h_hat (Real.log ↑p / (2 * Real.pi)) * ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ))) =
              ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ) *
                (χ ↑p * h_hat (-(Real.log ↑p / (2 * Real.pi))) * Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p)) +
                 (starRingEnd ℂ) (χ ↑p) * h_hat (Real.log ↑p / (2 * Real.pi)) * Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p))) := by ring
          rw [h_rhs_eq, Complex.re_ofReal_mul]
        rw [h_sum_eq]
        have h2pi_le : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
        calc (1 / (2 * Real.pi)) * |(D₁ χ).re + (star (D₂ χ)).re|
            ≤ 1 * (|(D₁ χ).re| + |(star (D₂ χ)).re|) := by
              gcongr; exact abs_add_le _ _
          _ ≤ ‖D₁ χ‖ + ‖star (D₂ χ)‖ := by
              rw [one_mul]
              exact add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          _ = ‖D₁ χ‖ + ‖D₂ χ‖ := by rw [norm_star]
      have h_max : (‖D₁ χ‖ + ‖D₂ χ‖) ^ (2 * k) ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
        set m := max ‖D₁ χ‖ ‖D₂ χ‖
        calc (‖D₁ χ‖ + ‖D₂ χ‖) ^ (2 * k)
            ≤ (2 * m) ^ (2 * k) := by
              gcongr; linarith [le_max_left ‖D₁ χ‖ ‖D₂ χ‖, le_max_right ‖D₁ χ‖ ‖D₂ χ‖]
          _ = 4 ^ k * m ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
              gcongr
              rcases le_total ‖D₁ χ‖ ‖D₂ χ‖ with h | h
              · simp only [m, max_eq_right h]; linarith [pow_nonneg (norm_nonneg (D₁ χ)) (2 * k)]
              · simp only [m, max_eq_left h]; linarith [pow_nonneg (norm_nonneg (D₂ χ)) (2 * k)]
      exact (pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)).trans h_max
    have h_poly_bound : ∀ (b : ℕ → ℂ),
        (∀ p ∈ primes, ‖b p‖ ≤ (Real.log p / Real.sqrt p) *
          max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) →
        ∑ χ : DirichletCharacter ℂ q, ‖∑ p ∈ primes, b p * χ p‖ ^ (2 * k) ≤
          (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k := by
      intro b hb
      set D : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b p * χ p
      let fiber : ℕ → Finset (Fin k → ℕ) := fun n =>
        (Fintype.piFinset (fun _ : Fin k => primes)).filter (fun f => (∏ i, f i) = n)
      let a : ℕ → ℂ := fun n => ∑ f ∈ fiber n, ∏ i, b (f i)
      have h_pow_eq : ∀ χ : DirichletCharacter ℂ q, (D χ) ^ k = ∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n := by
        intro χ
        dsimp only [D]
        rw [Finset.sum_pow']
        have h_maps : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primes),
            (∏ i : Fin k, f i) ∈ Finset.Icc 1 (P ^ k) := by
          intro f hf
          rw [Fintype.mem_piFinset] at hf
          rw [Finset.mem_Icc]
          refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
          calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
            _ = P ^ k := by simp
        rw [← Finset.sum_fiberwise_of_maps_to h_maps]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [a, fiber]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
        rw [Finset.prod_mul_distrib, ← hf.2]
        congr 1
        push_cast
        rw [map_prod]
      have h_norm_eq : ∀ χ : DirichletCharacter ℂ q, ‖∑ p ∈ primes, b p * χ p‖ ^ (2 * k) =
          ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 := by
        intro χ
        rw [mul_comm 2 k, pow_mul, ← norm_pow]
        change ‖(D χ) ^ k‖ ^ 2 = _
        rw [h_pow_eq χ]
      simp_rw [h_norm_eq]
      have hPk_lt_q : P ^ k < q := by
        have h1 : ((P ^ k : ℕ) : ℝ) < (q : ℝ) := by
          have hP_le : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
          calc ((P ^ k : ℕ) : ℝ) = (P : ℝ) ^ k := by push_cast; rfl
            _ ≤ X ^ k := pow_le_pow_left₀ (Nat.cast_nonneg P) hP_le k
            _ < q := hXk
        exact_mod_cast h1
      have h_orth : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 ≤
          (Nat.totient q : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := by
        have h_c_eq : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℝ) : ℂ) =
            ∑ m ∈ Finset.Icc 1 (P ^ k), ∑ n ∈ Finset.Icc 1 (P ^ k),
              a m * star (a n) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ n) := by
          push_cast
          have h_term : ∀ χ : DirichletCharacter ℂ q,
              (‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℂ) =
              ∑ m ∈ Finset.Icc 1 (P ^ k), ∑ n ∈ Finset.Icc 1 (P ^ k),
                a m * star (a n) * (χ m * star (χ n)) := by
            intro χ
            rw [← Complex.mul_conj', map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [map_mul, Complex.star_def]; ring
          simp_rw [h_term]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
        have h_inner : ∀ m ∈ Finset.Icc 1 (P ^ k), ∀ n ∈ Finset.Icc 1 (P ^ k), m ≠ n →
            ∑ χ : DirichletCharacter ℂ q, χ m * star (χ n) = 0 := by
          intro m hm n hn hmn
          simp only [Finset.mem_Icc] at hm hn
          by_cases hum : IsUnit (m : ZMod q)
          · by_cases hun : IsUnit (n : ZMod q)
            · have h_star : ∀ χ : DirichletCharacter ℂ q,
                  star (χ n) = χ ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
                intro χ
                have hmul1 : χ n * χ ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
                  have h_umul : (n : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
                    calc (n : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q)
                        = ((hun.unit : (ZMod q)ˣ) : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
                          rw [hun.unit_spec]
                      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
                  rw [← map_mul, h_umul, map_one]
                have hχn_ne : χ n ≠ 0 := fun h0 => by simp [h0] at hmul1
                have hnorm1 : ‖χ n‖ = 1 := dirichletChar_norm_eq_one χ hχn_ne
                have hmul2 : χ n * star (χ n) = 1 := by
                  rw [Complex.star_def, Complex.mul_conj', hnorm1]
                  norm_num
                exact mul_left_cancel₀ hχn_ne (hmul2.trans hmul1.symm)
              have h_prod : ∀ χ : DirichletCharacter ℂ q,
                  χ m * star (χ n) = χ (((hun.unit⁻¹ * hum.unit : (ZMod q)ˣ) : ZMod q)) := by
                intro χ
                rw [h_star χ, ← map_mul]
                congr 1
                push_cast
                rw [mul_comm, hum.unit_spec]
              simp_rw [h_prod]
              have ha_ne1 : (((hun.unit⁻¹ * hum.unit : (ZMod q)ˣ) : ZMod q)) ≠ 1 := by
                intro heq
                have hu_eq : hun.unit⁻¹ * hum.unit = 1 := Units.ext (by simpa using heq)
                have hum_eq : hum.unit = hun.unit := (eq_of_inv_mul_eq_one hu_eq).symm
                have hmn_zmod : (m : ZMod q) = (n : ZMod q) := by
                  rw [← hum.unit_spec, ← hun.unit_spec, hum_eq]
                have hm_lt : m < q := hm.2.trans_lt hPk_lt_q
                have hn_lt : n < q := hn.2.trans_lt hPk_lt_q
                have hval : m = n := by
                  have := congr_arg ZMod.val hmn_zmod
                  rwa [ZMod.val_natCast_of_lt hm_lt, ZMod.val_natCast_of_lt hn_lt] at this
                exact hmn hval
              haveI : NeZero q := ⟨hq_ne⟩
              exact DirichletCharacter.sum_characters_eq_zero (R := ℂ) ha_ne1
            · refine Finset.sum_eq_zero fun χ _ => ?_
              rw [MulChar.map_nonunit χ hun, star_zero, mul_zero]
          · refine Finset.sum_eq_zero fun χ _ => ?_
            rw [MulChar.map_nonunit χ hum, zero_mul]
        have h_diag : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℝ) : ℂ) =
            ∑ m ∈ Finset.Icc 1 (P ^ k), a m * star (a m) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m) := by
          rw [h_c_eq]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.sum_eq_single m (fun n hn hnm => by rw [h_inner m hm n hn hnm.symm, mul_zero])
            (fun hm' => absurd hm hm')]
        have h_re := congr_arg Complex.re h_diag
        simp only [Complex.ofReal_re, Complex.re_sum] at h_re
        rw [h_re]
        calc ∑ m ∈ Finset.Icc 1 (P ^ k), (a m * star (a m) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m)).re
            = ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 * ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 := by
              refine Finset.sum_congr rfl fun m _ => ?_
              have h1 : a m * star (a m) = ((‖a m‖ ^ 2 : ℝ) : ℂ) := by
                rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
              have h2 : ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m) =
                  ((∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 : ℝ) : ℂ) := by
                push_cast
                refine Finset.sum_congr rfl fun χ _ => ?_
                rw [Complex.star_def, Complex.mul_conj']
              rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]
          _ ≤ ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 * (Nat.totient q : ℝ) := by
              refine Finset.sum_le_sum fun m _ => ?_
              gcongr
              have hχ_le : ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 ≤
                  ∑ _χ : DirichletCharacter ℂ q, (1 : ℝ) := by
                refine Finset.sum_le_sum fun χ _ => ?_
                by_cases h0 : χ m = 0
                · simp [h0]
                · rw [dirichletChar_norm_eq_one χ h0, one_pow]
              calc ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2
                  ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) := by simpa using hχ_le
                _ = (Nat.totient q : ℝ) := by
                    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
          _ = (Nat.totient q : ℝ) * ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 := by
              rw [← Finset.sum_mul, mul_comm]
      have h_cs : ∀ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤ (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
        intro n _
        dsimp only [a]
        have h1 : ‖∑ f ∈ fiber n, ∏ i, b (f i)‖ ^ 2 ≤ (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
        have h2 : (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 ≤ (fiber n).card * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have h_card : (fiber n).card ≤ k.factorial :=
          prime_tuple_fiber_card primes (fun p hp => (Finset.mem_filter.mp hp).2) k n
        have h3 : ((fiber n).card : ℝ) * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 ≤
            (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
          have h_eq : ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 = ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [norm_prod, Finset.prod_pow]
          rw [h_eq]; gcongr
        exact h1.trans (h2.trans h3)
      have h_sum_a : ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤
          (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
        calc ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2
            ≤ ∑ n ∈ Finset.Icc 1 (P ^ k), (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 :=
              Finset.sum_le_sum h_cs
          _ = (k.factorial : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
              rw [← Finset.mul_sum]
          _ = (k.factorial : ℝ) * ∑ f ∈ Fintype.piFinset (fun _ : Fin k => primes), ∏ i, ‖b (f i)‖ ^ 2 := by
              congr 1
              refine Finset.sum_fiberwise_of_maps_to (fun f hf => ?_) _
              rw [Fintype.mem_piFinset] at hf
              rw [Finset.mem_Icc]
              refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
              calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                    Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
                _ = P ^ k := by simp
          _ = (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
              rw [Finset.sum_pow']
      have h_l2_b : ∑ p ∈ primes, ‖b p‖ ^ 2 ≤ C_l2 * Real.log (Real.log X) := by
        calc ∑ p ∈ primes, ‖b p‖ ^ 2
            ≤ ∑ p ∈ primes, ((Real.log p / Real.sqrt p) *
                max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) ^ 2 := by
              refine Finset.sum_le_sum fun p hp => ?_
              exact pow_le_pow_left₀ (norm_nonneg _) (hb p hp) 2
          _ ≤ C_l2 * Real.log (Real.log X) := hl2 Δ M hΔ hInt hL1
      have h_fac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast factorial_le_pow k
      calc ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2
          ≤ (Nat.totient q : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := h_orth
        _ ≤ (Nat.totient q : ℝ) * ((k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k) := by gcongr
        _ ≤ (Nat.totient q : ℝ) * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ = (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k := by
            rw [← mul_pow]; ring_nf
    have hb₁ : ∀ p ∈ primes, ‖b₁ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₁]
      have he : ‖Complex.exp (-Complex.I * t₀ * Real.log p)‖ = 1 := by
        have : -Complex.I * ↑t₀ * ↑(Real.log p) = ((-t₀ * Real.log p : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hb₂ : ∀ p ∈ primes, ‖b₂ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₂]
      have he : ‖Complex.exp (-Complex.I * t₀ * Real.log p)‖ = 1 := by
        have : -Complex.I * ↑t₀ * ↑(Real.log p) = ((-t₀ * Real.log p : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, he, mul_one, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    have hloglogX_ge : 0 ≤ Real.log (Real.log X) := by
      rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
      apply Real.log_nonneg
      have : 1 ≤ Δ := hΔ₀.trans hΔ
      nlinarith [Real.two_le_pi]
    calc (1 / (totientStar q : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            |primeSum1 q χ h_hat X t₀| ^ (2 * k)
        ≤ (1 / (totientStar q : ℝ)) *
            ∑ χ : DirichletCharacter ℂ q, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun χ _ _ => pow_nonneg (abs_nonneg _) _))
            (by positivity)
      _ ≤ (1 / (totientStar q : ℝ)) *
            ∑ χ : DirichletCharacter ℂ q, 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
          gcongr
          exact h_ptwise _
      _ = (1 / (totientStar q : ℝ)) *
            (4 ^ k * (∑ χ : DirichletCharacter ℂ q, ‖D₁ χ‖ ^ (2 * k) +
              ∑ χ : DirichletCharacter ℂ q, ‖D₂ χ‖ ^ (2 * k))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (1 / (totientStar q : ℝ)) *
            (4 ^ k * ((Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k +
              (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by
          have hb1_bd := h_poly_bound b₁ hb₁
          have hb2_bd := h_poly_bound b₂ hb₂
          change ∑ χ : DirichletCharacter ℂ q, ‖D₁ χ‖ ^ (2 * k) ≤ _ at hb1_bd
          change ∑ χ : DirichletCharacter ℂ q, ‖D₂ χ‖ ^ (2 * k) ≤ _ at hb2_bd
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (add_le_add hb1_bd hb2_bd) (by positivity))
            (by positivity)
      _ = ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (4 ^ k * (2 * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by ring
      _ ≤ ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (4 ^ k * (2 ^ k * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by
          gcongr
          have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
          simpa using this
      _ = ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (8 * C_l2 * k * Real.log (Real.log X)) ^ k := by
          rw [← mul_pow, ← mul_pow]; ring_nf
      _ ≤ ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (B * k * Real.log (Real.log X)) ^ k := by
          gcongr
          exact le_max_left _ _

end PolarEvaluation
