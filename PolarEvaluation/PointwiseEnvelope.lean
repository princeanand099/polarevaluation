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
  sorry

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
        · have : Real.exp 1 ≤ t := ht
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
