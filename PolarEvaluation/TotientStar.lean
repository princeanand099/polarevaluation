import PolarEvaluation.Basic
import PolarEvaluation.PrimeMoments

/-!
# Totient Ratio Bound `φ(q) / φ*(q)`
-/

noncomputable section

open Complex Real Filter Topology Classical

namespace PolarEvaluation

private lemma totientStar_mul_ge (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hab : Nat.Coprime a b) :
    totientStar a * totientStar b ≤ totientStar (a * b) := by
  classical
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a * b) := ⟨by positivity⟩
  let ha_dvd : a ∣ a * b := dvd_mul_right a b
  let hb_dvd : b ∣ a * b := dvd_mul_left b a
  let S_a := Finset.univ.filter (fun χ : DirichletCharacter ℂ a => χ.IsPrimitive)
  let S_b := Finset.univ.filter (fun χ : DirichletCharacter ℂ b => χ.IsPrimitive)
  let S_ab := Finset.univ.filter (fun χ : DirichletCharacter ℂ (a * b) => χ.IsPrimitive)
  let F : DirichletCharacter ℂ a × DirichletCharacter ℂ b → DirichletCharacter ℂ (a * b) :=
    fun p => DirichletCharacter.changeLevel ha_dvd p.1 * DirichletCharacter.changeLevel hb_dvd p.2
  have h_mem : ∀ p ∈ S_a ×ˢ S_b, F p ∈ S_ab := by
    rintro ⟨χ₁, χ₂⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, S_a, S_b, S_ab] at hp ⊢
    rcases hp with ⟨h1, h2⟩
    let ψ₁ := DirichletCharacter.changeLevel ha_dvd χ₁
    let ψ₂ := DirichletCharacter.changeLevel hb_dvd χ₂
    have hψ₁_c : ψ₁.conductor = a :=
      (DirichletCharacter.conductor_changeLevel χ₁ ha_dvd).trans (DirichletCharacter.isPrimitive_def.mp h1)
    have hψ₂_c : ψ₂.conductor = b :=
      (DirichletCharacter.conductor_changeLevel χ₂ hb_dvd).trans (DirichletCharacter.isPrimitive_def.mp h2)
    have h_dvd_ab : (ψ₁ * ψ₂).conductor ∣ a * b :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (ψ₁ * ψ₂) dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet (ψ₁ * ψ₂))
    have ha_dvd_c : a ∣ (ψ₁ * ψ₂).conductor := by
      have h_eq : ψ₁ = (ψ₁ * ψ₂) * ψ₂⁻¹ := (mul_inv_cancel_right ψ₁ ψ₂).symm
      have h_lcm := DirichletCharacter.conductor_mul_dvd_lcm_conductor (ψ₁ * ψ₂) ψ₂⁻¹
      rw [← h_eq, hψ₁_c, DirichletCharacter.conductor_inv, hψ₂_c] at h_lcm
      exact hab.dvd_of_dvd_mul_right (h_lcm.trans (Nat.lcm_dvd_mul _ _))
    have hb_dvd_c : b ∣ (ψ₁ * ψ₂).conductor := by
      have h_eq : ψ₂ = (ψ₁ * ψ₂) * ψ₁⁻¹ := by
        rw [mul_comm ψ₁ ψ₂]; exact (mul_inv_cancel_right ψ₂ ψ₁).symm
      have h_lcm := DirichletCharacter.conductor_mul_dvd_lcm_conductor (ψ₁ * ψ₂) ψ₁⁻¹
      rw [← h_eq, hψ₂_c, DirichletCharacter.conductor_inv, hψ₁_c] at h_lcm
      exact hab.symm.dvd_of_dvd_mul_right (h_lcm.trans (Nat.lcm_dvd_mul _ _))
    exact DirichletCharacter.isPrimitive_def.mpr
      (Nat.dvd_antisymm h_dvd_ab (hab.mul_dvd_of_dvd_of_dvd ha_dvd_c hb_dvd_c))
  have h_inj : Set.InjOn F (S_a ×ˢ S_b : Finset (DirichletCharacter ℂ a × DirichletCharacter ℂ b)) := by
    rintro ⟨χ₁, χ₂⟩ _ ⟨χ₁', χ₂'⟩ _ heq
    have h_eq1 : χ₁ = χ₁' := by
      ext u
      by_cases hu : IsUnit u
      · obtain ⟨k, hk_a, hk_b⟩ := Nat.chineseRemainder hab u.val 1
        have hku : (k : ZMod a) = u := by
          rw [← ZMod.natCast_zmod_val u]
          exact (ZMod.natCast_eq_natCast_iff k u.val a).mpr hk_a
        have hk1 : (k : ZMod b) = 1 := by
          simpa using (ZMod.natCast_eq_natCast_iff k 1 b).mpr hk_b
        have hcop_a : IsCoprime (k : ℤ) (a : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hku] using hu
        have hcop_b : IsCoprime (k : ℤ) (b : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod b))
        have hcop_ab : IsCoprime (k : ℤ) ((a * b : ℕ) : ℤ) := by
          push_cast; exact hcop_a.mul_right hcop_b
        have hval := congr_arg (fun (χ : DirichletCharacter ℂ (a * b)) => χ (k : ZMod (a * b))) heq
        dsimp only [F, MulChar.mul_apply] at hval
        have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁ hcop_ab
        have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂ hcop_ab
        have hc1' := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁' hcop_ab
        have hc2' := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂' hcop_ab
        simp only [Int.cast_natCast] at hc1 hc2 hc1' hc2'
        rw [hc1, hc2, hc1', hc2', hku, hk1, MulChar.map_one, mul_one, mul_one] at hval
        exact hval
      · simp [MulChar.map_nonunit hu]
    have h_eq2 : χ₂ = χ₂' := by
      ext u
      by_cases hu : IsUnit u
      · obtain ⟨k, hk_a, hk_b⟩ := Nat.chineseRemainder hab 1 u.val
        have hk1 : (k : ZMod a) = 1 := by
          simpa using (ZMod.natCast_eq_natCast_iff k 1 a).mpr hk_a
        have hku : (k : ZMod b) = u := by
          rw [← ZMod.natCast_zmod_val u]
          exact (ZMod.natCast_eq_natCast_iff k u.val b).mpr hk_b
        have hcop_a : IsCoprime (k : ℤ) (a : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod a))
        have hcop_b : IsCoprime (k : ℤ) (b : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hku] using hu
        have hcop_ab : IsCoprime (k : ℤ) ((a * b : ℕ) : ℤ) := by
          push_cast; exact hcop_a.mul_right hcop_b
        have hval := congr_arg (fun (χ : DirichletCharacter ℂ (a * b)) => χ (k : ZMod (a * b))) heq
        dsimp only [F, MulChar.mul_apply] at hval
        have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁ hcop_ab
        have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂ hcop_ab
        have hc1' := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁' hcop_ab
        have hc2' := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂' hcop_ab
        simp only [Int.cast_natCast] at hc1 hc2 hc1' hc2'
        rw [hc1, hc2, hc1', hc2', hk1, hku, MulChar.map_one, one_mul, one_mul] at hval
        exact hval
      · simp [MulChar.map_nonunit hu]
    exact Prod.ext h_eq1 h_eq2
  have h_card := Finset.card_le_card_of_injOn F h_mem h_inj
  rw [Finset.card_product] at h_card
  simpa [totientStar, S_a, S_b, S_ab] using h_card

private lemma totientStar_prime_ge (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    totientStar p ≥ p - 2 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_sub : Finset.univ.erase (1 : DirichletCharacter ℂ p) ⊆
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive) := by
    intro χ hχ
    rw [Finset.mem_erase] at hχ
    rw [Finset.mem_filter, Finset.mem_univ, true_and, DirichletCharacter.isPrimitive_def]
    have h_dvd : χ.conductor ∣ p :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ)
    rcases (Nat.dvd_prime hp).mp h_dvd with h1 | hp_eq
    · exfalso
      have h_mem1 : 1 ∈ χ.conductorSet := by
        rw [DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (one_dvd p), h1]
      rw [DirichletCharacter.mem_conductorSet_iff] at h_mem1
      rcases h_mem1 with ⟨hd1, χ₀, rfl⟩
      have hcard1 : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
        rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity 1 ℂ, Nat.totient_one]
      haveI : Subsingleton (DirichletCharacter ℂ 1) := Fintype.card_le_one_iff_subsingleton.mp hcard1.le
      have hχ₀ : χ₀ = 1 := Subsingleton.elim χ₀ 1
      rw [hχ₀, map_one] at hχ
      exact hχ.1 rfl
    · exact hp_eq
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity p ℂ, Nat.totient_prime hp] at h_card
  simpa [totientStar] using (show p - 2 ≤ totientStar p by omega)

private lemma totientStar_prime_pow_ge (p e : ℕ) (hp : Nat.Prime p) (he : e ≥ 2) :
    totientStar (p ^ e) ≥ Nat.totient (p ^ e) - Nat.totient (p ^ (e - 1)) := by
  classical
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  let hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (Nat.sub_le e 1)
  let S_nonprim : Finset (DirichletCharacter ℂ (p ^ e)) :=
    Finset.univ.image (DirichletCharacter.changeLevel hd)
  have h_sub : Finset.univ \ S_nonprim ⊆
      Finset.univ.filter (fun χ : DirichletCharacter ℂ (p ^ e) => χ.IsPrimitive) := by
    intro χ hχ
    rw [Finset.mem_sdiff] at hχ
    rw [Finset.mem_filter, Finset.mem_univ, true_and, DirichletCharacter.isPrimitive_def]
    have h_dvd : χ.conductor ∣ p ^ e :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ)
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp h_dvd
    by_cases hke : k = e
    · rw [hk_eq, hke]
    · exfalso
      have hk_le1 : k ≤ e - 1 := by omega
      have h_dvd1 : χ.conductor ∣ p ^ (e - 1) := by rw [hk_eq]; exact pow_dvd_pow p hk_le1
      have h_mem1 : p ^ (e - 1) ∈ χ.conductorSet :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr h_dvd1
      rw [DirichletCharacter.mem_conductorSet_iff] at h_mem1
      rcases h_mem1 with ⟨_, χ₀, hχ₀⟩
      apply hχ.2
      exact Finset.mem_image.mpr ⟨χ₀, Finset.mem_univ _, hχ₀.symm⟩
  have h_card := Finset.card_le_card h_sub
  have h_sdiff : (Finset.univ \ S_nonprim).card ≥
      Fintype.card (DirichletCharacter ℂ (p ^ e)) - S_nonprim.card := by
    have := Finset.card_sdiff_add_card_inter Finset.univ S_nonprim
    rw [Finset.univ_inter] at this
    omega
  have h_nonprim_le : S_nonprim.card ≤ Nat.totient (p ^ (e - 1)) := by
    calc S_nonprim.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ (p ^ (e - 1)))).card :=
          Finset.card_image_le
      _ = Fintype.card (DirichletCharacter ℂ (p ^ (e - 1))) := Finset.card_univ
      _ = Nat.totient (p ^ (e - 1)) :=
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (p ^ (e - 1)) ℂ
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (p ^ e) ℂ] at h_sdiff
  have h_le : Nat.totient (p ^ e) - Nat.totient (p ^ (e - 1)) ≤ totientStar (p ^ e) := by
    dsimp only [totientStar]; omega
  exact h_le

private lemma two_exact_dvd_totientStar_zero (m : ℕ) (hm : m ≥ 1) (hcop : Nat.Coprime 2 m) :
    totientStar (2 * m) = 0 := by
  classical
  haveI : NeZero (2 * m) := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  let hm_dvd : m ∣ 2 * m := dvd_mul_left m 2
  have h_inj : Function.Injective (DirichletCharacter.changeLevel (R := ℂ) hm_dvd) := by
    intro χ₁ χ₂ heq
    ext u
    by_cases hu : IsUnit u
    · obtain ⟨k, hk_2, hk_m⟩ := Nat.chineseRemainder hcop 1 u.val
      have hk1 : (k : ZMod 2) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff k 1 2).mpr hk_2
      have hku : (k : ZMod m) = u := by
        rw [← ZMod.natCast_zmod_val u]
        exact (ZMod.natCast_eq_natCast_iff k u.val m).mpr hk_m
      have hcop_2 : IsCoprime (k : ℤ) (2 : ℤ) := by
        rw [← ZMod.isUnit_iff_coprime_int]
        simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod 2))
      have hcop_m : IsCoprime (k : ℤ) (m : ℤ) := by
        rw [← ZMod.isUnit_iff_coprime_int]
        simpa [hku] using hu
      have hcop_2m : IsCoprime (k : ℤ) ((2 * m : ℕ) : ℤ) := by
        push_cast; exact hcop_2.mul_right hcop_m
      have hval := congr_arg (fun (χ : DirichletCharacter ℂ (2 * m)) => χ (k : ZMod (2 * m))) heq
      have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hm_dvd χ₁ hcop_2m
      have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hm_dvd χ₂ hcop_2m
      simp only [Int.cast_natCast] at hc1 hc2
      rw [hc1, hc2, hku] at hval
      exact hval
    · simp [MulChar.map_nonunit hu]
  have h_card_eq : Fintype.card (DirichletCharacter ℂ m) = Fintype.card (DirichletCharacter ℂ (2 * m)) := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity m ℂ,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (2 * m) ℂ,
      Nat.totient_mul hcop, Nat.totient_two, one_mul]
  have h_surj : Function.Surjective (DirichletCharacter.changeLevel (R := ℂ) hm_dvd) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨h_inj, h_card_eq⟩ |>.2
  have h_empty : Finset.univ.filter (fun χ : DirichletCharacter ℂ (2 * m) => χ.IsPrimitive) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro χ _
    obtain ⟨χ₀, rfl⟩ := h_surj χ
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_changeLevel]
    have h_dvd : χ₀.conductor ∣ m :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ₀ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ₀)
    have h_le : χ₀.conductor ≤ m := Nat.le_of_dvd hm h_dvd
    omega
  simp [totientStar, h_empty]

lemma totient_div_totientStar_le (q : ℕ) (hq : q ≥ 3) (hqstar : totientStar q ≥ 1) :
    (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤ 2 * Real.exp 60 * (Real.log q) ^ 30 := by
  classical
  have hq0 : q ≠ 0 := by omega
  have h_v2_ne1 : q.factorization 2 ≠ 1 := by
    intro h1
    have h_ord := Nat.ordProj_mul_ordCompl_eq_self q 2
    have h_cop : Nat.Coprime (2 ^ q.factorization 2) (q / 2 ^ q.factorization 2) :=
      Nat.coprime_ordCompl Nat.prime_two hq0
    rw [h1, pow_one] at h_ord h_cop
    have hm_pos : q / 2 ≥ 1 := by
      have : 2 * (q / 2) = q := h_ord
      omega
    have h0 := two_exact_dvd_totientStar_zero (q / 2) hm_pos h_cop
    rw [h_ord] at h0
    omega
  have h_prod_star : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∏ p ∈ s, totientStar (p ^ (q.factorization p)) ≤
        totientStar (∏ p ∈ s, p ^ (q.factorization p)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      have h1 : totientStar 1 = 1 := by
        have h_card : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
          rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity 1 ℂ, Nat.totient_one]
        haveI : Unique (DirichletCharacter ℂ 1) := Fintype.card_eq_one_iff_unique.mp h_card |>.some
        have h_eq : Finset.univ.filter (fun χ : DirichletCharacter ℂ 1 => χ.IsPrimitive) = Finset.univ := by
          ext χ; simp [Subsingleton.elim χ 1, DirichletCharacter.isPrimitive_one_level_one]
        simp [totientStar, h_eq, h_card]
      omega
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_prime : Nat.Prime a := hs a (Finset.mem_insert_self _ _)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have ha_pos : a ^ q.factorization a ≥ 1 := Nat.one_le_pow _ _ ha_prime.pos
      have hs_pos : ∏ p ∈ s, p ^ q.factorization p ≥ 1 :=
        Finset.prod_pos fun p hp => Nat.pow_pos (hs_prime p hp).pos
      have h_cop : Nat.Coprime (a ^ q.factorization a) (∏ p ∈ s, p ^ q.factorization p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_prime := hs_prime p hp
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_prime hp_prime).mpr hne).pow _ _
      calc totientStar (a ^ q.factorization a) * ∏ p ∈ s, totientStar (p ^ q.factorization p)
          ≤ totientStar (a ^ q.factorization a) * totientStar (∏ p ∈ s, p ^ q.factorization p) :=
            Nat.mul_le_mul_left _ (ih hs_prime)
        _ ≤ totientStar (a ^ q.factorization a * ∏ p ∈ s, p ^ q.factorization p) :=
            totientStar_mul_ge _ _ ha_pos hs_pos h_cop
  have h_prod_tot : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      Nat.totient (∏ p ∈ s, p ^ (q.factorization p)) =
        ∏ p ∈ s, Nat.totient (p ^ (q.factorization p)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_prime : Nat.Prime a := hs a (Finset.mem_insert_self _ _)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have h_cop : Nat.Coprime (a ^ q.factorization a) (∏ p ∈ s, p ^ q.factorization p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_prime := hs_prime p hp
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_prime hp_prime).mpr hne).pow _ _
      rw [Nat.totient_mul h_cop, ih hs_prime]
  have h_fac_eq : ∏ p ∈ q.primeFactors, p ^ q.factorization p = q :=
    Nat.factorization_prod_pow_eq_self hq0
  have h_pf_prime : ∀ p ∈ q.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h_star_lb : ∏ p ∈ q.primeFactors, totientStar (p ^ q.factorization p) ≤ totientStar q := by
    simpa [h_fac_eq] using h_prod_star q.primeFactors h_pf_prime
  have h_tot_eq : Nat.totient q = ∏ p ∈ q.primeFactors, Nat.totient (p ^ q.factorization p) := by
    simpa [h_fac_eq] using h_prod_tot q.primeFactors h_pf_prime
  have h_ratio_term : ∀ p ∈ q.primeFactors,
      (Nat.totient (p ^ q.factorization p) : ℝ) / (totientStar (p ^ q.factorization p) : ℝ) ≤
        if p = 2 then 2 else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp_prime hq0 (Nat.dvd_of_mem_primeFactors hp)
    split_ifs with hp2
    · subst hp2
      have he2 : 2 ≤ q.factorization 2 := by omega
      have h_star := totientStar_prime_pow_ge 2 (q.factorization 2) Nat.prime_two he2
      have h_t1 : Nat.totient (2 ^ q.factorization 2) = 2 ^ (q.factorization 2 - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t2 : Nat.totient (2 ^ (q.factorization 2 - 1)) = 2 ^ (q.factorization 2 - 2) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t_eq : Nat.totient (2 ^ q.factorization 2) = 2 * Nat.totient (2 ^ (q.factorization 2 - 1)) := by
        rw [h_t1, h_t2, ← pow_succ']; congr 1; omega
      have h_s_pos : 1 ≤ totientStar (2 ^ q.factorization 2) := by
        have : 1 ≤ Nat.totient (2 ^ (q.factorization 2 - 1)) := by rw [h_t2]; exact Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [div_le_iff₀ (by exact_mod_cast h_s_pos)]
      norm_cast; omega
    · have hp3 : p ≥ 3 := by have := hp_prime.two_le; omega
      have hp_real : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      rcases Nat.eq_or_lt_of_le he_pos with he1 | he2
      · rw [← he1, pow_one]
        have h_star := totientStar_prime_ge p hp_prime hp3
        rw [Nat.totient_prime hp_prime]
        have h_s_pos : (0 : ℝ) < totientStar p := by
          have : 1 ≤ p - 2 := by omega
          exact_mod_cast (show 1 ≤ totientStar p by omega)
        have h_s_ge : (p : ℝ) - 2 ≤ totientStar p := by
          have : (p - 2 : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
          rw [← this]; exact_mod_cast h_star
        have h_p1 : (p - 1 : ℝ) = ((p - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [← h_p1]
        calc ((p : ℝ) - 1) / (totientStar p : ℝ)
            ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by gcongr; linarith
          _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
              rw [div_pow, div_le_div_iff₀ (by linarith) (sq_pos_of_pos (by linarith))]
              nlinarith
      · have h_star := totientStar_prime_pow_ge p (q.factorization p) hp_prime he2
        have h_t1 : Nat.totient (p ^ q.factorization p) = p ^ (q.factorization p - 1) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_t2 : Nat.totient (p ^ (q.factorization p - 1)) = p ^ (q.factorization p - 2) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_s_lb : p ^ (q.factorization p - 2) * (p - 1) ^ 2 ≤ totientStar (p ^ q.factorization p) := by
          have h_pow : p ^ (q.factorization p - 1) = p ^ (q.factorization p - 2) * p := by
            rw [← pow_succ]; congr 1; omega
          rw [h_t1, h_t2, h_pow] at h_star
          have h_sub : p ^ (q.factorization p - 2) * p * (p - 1) - p ^ (q.factorization p - 2) * (p - 1) =
              p ^ (q.factorization p - 2) * (p - 1) ^ 2 := by
            zify [show 1 ≤ p by omega]; ring
          omega
        have h_s_pos : (0 : ℝ) < totientStar (p ^ q.factorization p) := by
          have : 1 ≤ p ^ (q.factorization p - 2) * (p - 1) ^ 2 :=
            Nat.mul_pos (Nat.pow_pos hp_prime.pos) (sq_pos_of_pos (by omega))
          exact_mod_cast this.trans_le h_s_lb
        have h_s_real : ((p : ℝ) ^ (q.factorization p - 2)) * ((p : ℝ) - 1) ^ 2 ≤
            (totientStar (p ^ q.factorization p) : ℝ) := by
          have h1 : ((p ^ (q.factorization p - 2) * (p - 1) ^ 2 : ℕ) : ℝ) ≤ totientStar (p ^ q.factorization p) := by
            exact_mod_cast h_s_lb
          push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at h1
          exact h1
        have h_t_real : (Nat.totient (p ^ q.factorization p) : ℝ) =
            (p : ℝ) ^ (q.factorization p - 1) * ((p : ℝ) - 1) := by
          rw [h_t1]; push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; rfl
        have h_pow_r : (p : ℝ) ^ (q.factorization p - 1) = (p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) := by
          rw [← pow_succ]; congr 1; omega
        rw [h_t_real, h_pow_r]
        calc ((p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) * ((p : ℝ) - 1)) / (totientStar (p ^ q.factorization p) : ℝ)
            ≤ ((p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) * ((p : ℝ) - 1)) /
                ((p : ℝ) ^ (q.factorization p - 2) * ((p : ℝ) - 1) ^ 2) := by
              gcongr; positivity
          _ = (p : ℝ) / ((p : ℝ) - 1) := by
              have hne1 : (p : ℝ) ^ (q.factorization p - 2) ≠ 0 := by positivity
              have hne2 : (p : ℝ) - 1 ≠ 0 := by linarith
              field_simp [hne1, hne2]
          _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
              have h1 : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by rw [one_le_div (by linarith)]; linarith
              nlinarith
  have h_star_pos_each : ∀ p ∈ q.primeFactors, 0 < (totientStar (p ^ q.factorization p) : ℝ) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp_prime hq0 (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp2 : p = 2
    · subst hp2
      have he2 : 2 ≤ q.factorization 2 := by omega
      have h_star := totientStar_prime_pow_ge 2 (q.factorization 2) Nat.prime_two he2
      have h_t1 : Nat.totient (2 ^ q.factorization 2) = 2 ^ (q.factorization 2 - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t2 : Nat.totient (2 ^ (q.factorization 2 - 1)) = 2 ^ (q.factorization 2 - 2) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have : 1 ≤ totientStar (2 ^ q.factorization 2) := by
        have h_pow : 2 ^ (q.factorization 2 - 1) = 2 * 2 ^ (q.factorization 2 - 2) := by
          rw [← pow_succ']; congr 1; omega
        have : 1 ≤ 2 ^ (q.factorization 2 - 2) := Nat.one_le_pow _ _ (by norm_num)
        omega
      exact_mod_cast this
    · have hp3 : p ≥ 3 := by have := hp_prime.two_le; omega
      rcases Nat.eq_or_lt_of_le he_pos with he1 | he2
      · rw [← he1, pow_one]
        have h_star := totientStar_prime_ge p hp_prime hp3
        exact_mod_cast (show 1 ≤ totientStar p by omega)
      · have h_star := totientStar_prime_pow_ge p (q.factorization p) hp_prime he2
        have h_t1 : Nat.totient (p ^ q.factorization p) = p ^ (q.factorization p - 1) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_t2 : Nat.totient (p ^ (q.factorization p - 1)) = p ^ (q.factorization p - 2) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have : 1 ≤ totientStar (p ^ q.factorization p) := by
          have h_pow : p ^ (q.factorization p - 1) = p ^ (q.factorization p - 2) * p := by
            rw [← pow_succ]; congr 1; omega
          rw [h_t1, h_t2, h_pow] at h_star
          have h_sub : p ^ (q.factorization p - 2) * p * (p - 1) - p ^ (q.factorization p - 2) * (p - 1) =
              p ^ (q.factorization p - 2) * (p - 1) ^ 2 := by
            zify [show 1 ≤ p by omega]; ring
          have : 1 ≤ p ^ (q.factorization p - 2) * (p - 1) ^ 2 :=
            Nat.mul_pos (Nat.pow_pos hp_prime.pos) (sq_pos_of_pos (by omega))
          omega
        exact_mod_cast this
  have h_prod_pos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (totientStar (p ^ q.factorization p) : ℝ) :=
    Finset.prod_pos h_star_pos_each
  have h_ratio_prod : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤
      2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    have h_le1 : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤
        ∏ p ∈ q.primeFactors, ((Nat.totient (p ^ q.factorization p) : ℝ) /
          (totientStar (p ^ q.factorization p) : ℝ)) := by
      rw [← Finset.prod_div_distrib]
      have h_num : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, (Nat.totient (p ^ q.factorization p) : ℝ) := by
        exact_mod_cast h_tot_eq
      have h_den : ∏ p ∈ q.primeFactors, (totientStar (p ^ q.factorization p) : ℝ) ≤ (totientStar q : ℝ) := by
        exact_mod_cast h_star_lb
      rw [h_num]
      exact div_le_div_of_nonneg_left (Finset.prod_nonneg fun p _ => by positivity) h_prod_pos h_den
    have h_le2 : ∏ p ∈ q.primeFactors, ((Nat.totient (p ^ q.factorization p) : ℝ) /
          (totientStar (p ^ q.factorization p) : ℝ)) ≤
        ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => h_ratio_term p hp)
    have h_split : ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
        2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
      by_cases h2 : 2 ∈ q.primeFactors
      · rw [← Finset.mul_prod_erase q.primeFactors _ h2, if_pos rfl]
        gcongr
        have h_er : q.primeFactors.erase 2 = q.primeFactors.filter (· ≠ 2) := by
          ext p; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
        rw [h_er]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rw [if_neg hp.2]
      · have h_f : q.primeFactors.filter (· ≠ 2) = q.primeFactors := by
          rw [Finset.filter_eq_self]; intro p hp hpe; exact h2 (hpe ▸ hp)
        rw [h_f]
        have h_eq : ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) =
            ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [if_neg (fun h => h2 (h ▸ hp))]
        rw [h_eq]
        have h_nn : 0 ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
          Finset.prod_nonneg fun p _ => by positivity
        linarith
    exact h_le1.trans (h_le2.trans h_split)
  have h_log_prod : Real.log (∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
      30 * Real.log (Real.log q) + 60 := by
    have h_pos_each : ∀ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≠ 0 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      positivity
    rw [Real.log_prod _ _ h_pos_each]
    have h_term : ∀ p ∈ q.primeFactors.filter (· ≠ 2),
        Real.log (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤ 3 * ((1 : ℝ) / p) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      rw [Real.log_pow, Nat.cast_ofNat]
      have h_log1 := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((p : ℝ) - 1) by positivity)
      have h_sub : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
        field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]; ring
      have h_le : 2 * (1 / ((p : ℝ) - 1)) ≤ 3 * (1 / (p : ℝ)) := by
        rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith
    have h_sum1 : ∑ p ∈ q.primeFactors.filter (· ≠ 2), Real.log (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
        3 * ∑ p ∈ q.primeFactors.filter (· ≠ 2), (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum h_term
    have h_sub_icc : q.primeFactors.filter (· ≠ 2) ⊆ (Finset.Icc 2 q).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp.1
      exact ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, Nat.le_of_dvd (by omega) hp_dvd⟩, hp_prime⟩
    have h_sum2 : ∑ p ∈ q.primeFactors.filter (· ≠ 2), (1 : ℝ) / p ≤
        ∑ p ∈ (Finset.Icc 2 q).filter Nat.Prime, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub_icc (fun p _ _ => by positivity)
    have h_mert := mertens_second q hq
    linarith
  have h_exp_prod : ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤
      Real.exp 60 * (Real.log q) ^ 30 := by
    have h_prod_pos2 : 0 < ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
      refine Finset.prod_pos fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      positivity
    have h_logq_pos : 0 < Real.log q := by
      apply Real.log_pos; exact_mod_cast (by omega : 1 < q)
    rw [← Real.exp_log h_prod_pos2]
    calc Real.exp (Real.log (∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2))
        ≤ Real.exp (30 * Real.log (Real.log q) + 60) := Real.exp_le_exp.mpr h_log_prod
      _ = Real.exp 60 * Real.exp ((30 : ℕ) * Real.log (Real.log q)) := by
          rw [Real.exp_add]; push_cast; ring_nf
      _ = Real.exp 60 * (Real.log q) ^ 30 := by
          rw [← Real.log_pow, Real.exp_log (pow_pos h_logq_pos 30)]
  calc (Nat.totient q : ℝ) / (totientStar q : ℝ)
      ≤ 2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := h_ratio_prod
    _ ≤ 2 * (Real.exp 60 * (Real.log q) ^ 30) := by gcongr
    _ = 2 * Real.exp 60 * (Real.log q) ^ 30 := by ring

end PolarEvaluation
