/- GID: D5/S3/Arith/PrimitiveRoot/SieveSevenFactors
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SieveSevenFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff; premises=D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_shapes,D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_candidates
   digest: Classification of the exceptional seven-prime sieve supports. -/
import D5.S3.Arith.PrimitiveRoot.SievePrimeFactors

/-! Finite branching of seven-prime supports with large reciprocal mass. -/

namespace D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
open scoped BigOperators
open SievePrimeFactors

private lemma gap {p : ℕ} (a b : ℕ) (hp : p.Prime) (ha : a ≤ p)
    (hg : ∀ t ∈ Finset.Ico a b, ¬t.Prime) : b ≤ p := by
  classical
  by_contra h
  exact hg p (Finset.mem_Ico.mpr ⟨ha, by omega⟩) hp

private lemma tail_le (q : Fin 7 → ℕ) (b : Fin 5 → ℕ)
    (hb : ∀ i, 0 < b i) (hle : ∀ i, b i ≤ q (Fin.natAdd 2 i)) :
    (∑ i : Fin 5, (q (Fin.natAdd 2 i) : ℝ)⁻¹) ≤
      ∑ i : Fin 5, (b i : ℝ)⁻¹ := by
  classical
  apply Finset.sum_le_sum
  intro i _
  exact inv_anti₀ (by exact_mod_cast hb i) (by exact_mod_cast hle i)

/-- A seven-prime support with excessive tail mass has one of ten explicit tails. -/
theorem seven_shapes (q : Fin 7 → ℕ) :
    (StrictMono q ∧ (∀ i, (q i).Prime) ∧
      (73 / 137 : ℝ) < ∑ i : Fin 5, (q (Fin.natAdd 2 i) : ℝ)⁻¹) ↔
    q 0 = 2 ∧ q 1 = 3 ∧ q 2 = 5 ∧ q 3 = 7 ∧ q 4 = 11 ∧
      ((q 5 = 13 ∧ q 6 ∈ ({17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ)) ∨
        (q 5 = 17 ∧ (q 6 = 19 ∨ q 6 = 23))) := by
  classical
  constructor
  · rintro ⟨hm, hp, hbad⟩
    norm_num [Fin.sum_univ_succ] at hbad
    have step (i j : Fin 7) (hij : i < j) : q i + 1 ≤ q j := hm hij
    have h2 : 5 ≤ q 2 := by
      simpa [firstEight] using
      prime_rank_lower q 2 (hm.strictMonoOn _) (fun j _ => hp j) (by decide)
    have h3 : 7 ≤ q 3 := by
      simpa [firstEight] using
      prime_rank_lower q 3 (hm.strictMonoOn _) (fun j _ => hp j) (by decide)
    have h4 : 11 ≤ q 4 := by
      simpa [firstEight] using
      prime_rank_lower q 4 (hm.strictMonoOn _) (fun j _ => hp j) (by decide)
    have h5 : 13 ≤ q 5 := by
      simpa [firstEight] using
      prime_rank_lower q 5 (hm.strictMonoOn _) (fun j _ => hp j) (by decide)
    have h6 : 17 ≤ q 6 := by
      simpa [firstEight] using
      prime_rank_lower q 6 (hm.strictMonoOn _) (fun j _ => hp j) (by decide)
    have q2 : q 2 = 5 := by
      by_contra h
      have a : 7 ≤ q 2 := gap 6 7 (hp 2) (by omega) (by decide)
      have b : 11 ≤ q 3 := gap 8 11 (hp 3) (by have := step 2 3 (by decide); omega)
        (by decide)
      have c : 13 ≤ q 4 := gap 12 13 (hp 4) (by have := step 3 4 (by decide); omega)
        (by decide)
      have d : 17 ≤ q 5 := gap 14 17 (hp 5) (by have := step 4 5 (by decide); omega)
        (by decide)
      have e : 19 ≤ q 6 := gap 18 19 (hp 6) (by have := step 5 6 (by decide); omega)
        (by decide)
      have hh := tail_le q ![7, 11, 13, 17, 19] (by decide)
        (by intro i; fin_cases i <;> dsimp <;> assumption)
      norm_num [Fin.sum_univ_succ] at hh
      linarith
    have q3 : q 3 = 7 := by
      by_contra h
      have b : 11 ≤ q 3 := gap 8 11 (hp 3) (by omega) (by decide)
      have c : 13 ≤ q 4 := gap 12 13 (hp 4) (by have := step 3 4 (by decide); omega)
        (by decide)
      have d : 17 ≤ q 5 := gap 14 17 (hp 5) (by have := step 4 5 (by decide); omega)
        (by decide)
      have e : 19 ≤ q 6 := gap 18 19 (hp 6) (by have := step 5 6 (by decide); omega)
        (by decide)
      have hh := tail_le q ![5, 11, 13, 17, 19] (by decide)
        (by intro i; fin_cases i <;> dsimp <;> assumption)
      norm_num [Fin.sum_univ_succ] at hh
      linarith
    have q4 : q 4 = 11 := by
      by_contra h
      have c : 13 ≤ q 4 := gap 12 13 (hp 4) (by omega) (by decide)
      have d : 17 ≤ q 5 := gap 14 17 (hp 5) (by have := step 4 5 (by decide); omega)
        (by decide)
      have e : 19 ≤ q 6 := gap 18 19 (hp 6) (by have := step 5 6 (by decide); omega)
        (by decide)
      have hh := tail_le q ![5, 7, 13, 17, 19] (by decide)
        (by intro i; fin_cases i <;> dsimp <;> assumption)
      norm_num [Fin.sum_univ_succ] at hh
      linarith
    have q01 : q 0 = 2 ∧ q 1 = 3 := by
      have h0 := (hp 0).two_le
      have h01 := step 0 1 (by decide)
      have h12 := step 1 2 (by decide)
      have h14 : q 1 ≠ 4 := by intro h; have := hp 1; norm_num [h] at this
      omega
    refine ⟨q01.1, q01.2, q2, q3, q4, ?_⟩
    have h5small : q 5 < 19 := by
      by_contra h
      have d : 19 ≤ q 5 := by omega
      have e : 23 ≤ q 6 := gap 20 23 (hp 6) (by have := step 5 6 (by decide); omega)
        (by decide)
      have hh := tail_le q ![5, 7, 11, 19, 23] (by decide)
        (by intro i; fin_cases i <;> dsimp <;> assumption)
      norm_num [Fin.sum_univ_succ] at hh
      linarith
    have h5cases : q 5 = 13 ∨ q 5 = 17 := by
      have hh : ∀ t ∈ Finset.Icc 13 18, t.Prime → t = 13 ∨ t = 17 := by decide
      exact hh _ (Finset.mem_Icc.mpr ⟨h5, by omega⟩) (hp 5)
    rcases h5cases with h13 | h17
    · left
      refine ⟨h13, ?_⟩
      have hlt : q 6 < 47 := by
        by_contra h
        have e : 47 ≤ q 6 := by omega
        have hh := tail_le q ![5, 7, 11, 13, 47] (by decide)
          (by intro i; fin_cases i <;> dsimp <;> assumption)
        norm_num [Fin.sum_univ_succ] at hh
        linarith
      have hh : ∀ t ∈ Finset.Icc 17 46, t.Prime →
          t ∈ ({17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) := by decide
      exact hh _ (Finset.mem_Icc.mpr ⟨h6, by omega⟩) (hp 6)
    · right
      refine ⟨h17, ?_⟩
      have hlo : 19 ≤ q 6 := gap 18 19 (hp 6)
        (by have := step 5 6 (by decide); omega) (by decide)
      have hlt : q 6 < 29 := by
        by_contra h
        have e : 29 ≤ q 6 := by omega
        have hh := tail_le q ![5, 7, 11, 17, 29] (by decide)
          (by intro i; fin_cases i <;> dsimp <;> first | assumption | omega)
        norm_num [Fin.sum_univ_succ] at hh
        linarith
      have hh : ∀ t ∈ Finset.Icc 19 28, t.Prime → t = 19 ∨ t = 23 := by decide
      exact hh _ (Finset.mem_Icc.mpr ⟨hlo, by omega⟩) (hp 6)
  · rintro ⟨h0, h1, h2, h3, h4, htail⟩
    have hstructure : StrictMono q ∧ ∀ i, (q i).Prime := by
      rcases htail with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · have hq : q = ![2, 3, 5, 7, 11, 13, q 6] := by
          funext i
          fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]
        rw [hq]
        have ht : ∀ v ∈ ({17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ),
            StrictMono (![2, 3, 5, 7, 11, 13, v]) ∧
              ∀ i : Fin 7, (![2, 3, 5, 7, 11, 13, v] i).Prime := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨by decide, by decide⟩
        exact ht (q 6) h6
      · have hq : q = ![2, 3, 5, 7, 11, 17, q 6] := by
          funext i
          fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]
        rw [hq]
        have ht : ∀ v ∈ ({19, 23} : Finset ℕ),
            StrictMono (![2, 3, 5, 7, 11, 17, v]) ∧
              ∀ i : Fin 7, (![2, 3, 5, 7, 11, 17, v] i).Prime := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> exact ⟨by decide, by decide⟩
        exact ht (q 6) (by simpa using h6)
    refine ⟨hstructure.1, hstructure.2, ?_⟩
    rcases htail with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h6
      rcases h6 with h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 <;>
        norm_num [Fin.sum_univ_succ, h2, h3, h4, h5, h6]
    · rcases h6 with h6 | h6 <;>
        norm_num [Fin.sum_univ_succ, h2, h3, h4, h5, h6]

/-- The interval, support size and strict reciprocal condition classify eight integers. -/
theorem seven_candidates (x : ℕ) :
    (3483482 ≤ x ∧ x < 4144141 ∧
      ∃ hc : (x - 1).primeFactors.card = 7,
        (73 / 137 : ℝ) < ∑ i : Fin 5,
          ((x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd 2 i) : ℝ)⁻¹) ↔
    x ∈ ({3573571, 4084081, 3993991, 3723721,
      3693691, 3873871, 3730651, 3612841} : Finset ℕ) := by
  classical
  constructor
  · rintro ⟨hlo, hhi, hc, hbad⟩
    let q := (x - 1).primeFactors.orderEmbOfFin hc
    obtain ⟨h0, h1, h2, h3, h4, htail⟩ := (seven_shapes q).mp ⟨q.strictMono,
      fun i => Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ hc i), hbad⟩
    have hprod : (∏ p ∈ (x - 1).primeFactors, p) = 2310 * q 5 * q 6 := by
      rw [← Finset.map_orderEmbOfFin_univ (x - 1).primeFactors hc, Finset.prod_map]
      change (∏ i : Fin 7, q i) = _
      simp [Fin.prod_univ_succ, h0, h1, h2, h3, h4]
      ring
    have hd := Nat.prod_primeFactors_dvd (x - 1)
    rw [hprod] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases htail with ⟨h13, hv⟩ | ⟨h17, hv⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv | hv | hv | hv | hv | hv | hv <;>
        rw [h13, hv] at hd <;>
        obtain ⟨m, hm⟩ := hd <;> norm_num at hm <;> omega
    · rcases hv with hv | hv <;>
        rw [h17, hv] at hd <;>
        obtain ⟨m, hm⟩ := hd <;> norm_num at hm <;> omega

  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3573571 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 17]
      have hq : f = fun i => (3573571 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3573571 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (4084081 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 17]
      have hq : f = fun i => (4084081 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (4084081 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3993991 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 19]
      have hq : f = fun i => (3993991 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3993991 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3723721 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 31]
      have hq : f = fun i => (3723721 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3723721 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3693691 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 41]
      have hq : f = fun i => (3693691 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3693691 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3873871 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 43]
      have hq : f = fun i => (3873871 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3873871 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3730651 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 17, 19]
      have hq : f = fun i => (3730651 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3730651 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]
    · refine ⟨by decide, by decide, ?_⟩
      have hc : (3612841 - 1 : ℕ).primeFactors.card = 7 := by decide +kernel
      refine ⟨hc, ?_⟩
      let f : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 17, 23]
      have hq : f = fun i => (3612841 - 1 : ℕ).primeFactors.orderEmbOfFin hc i := by
        apply Finset.orderEmbOfFin_unique hc
        · intro i
          fin_cases i <;> decide +kernel
        · decide
      change (73 / 137 : ℝ) < ∑ i : Fin 5,
        ((fun j => (3612841 - 1 : ℕ).primeFactors.orderEmbOfFin hc j)
          (Fin.natAdd 2 i) : ℝ)⁻¹
      rw [← hq]
      norm_num [f, Fin.sum_univ_succ]

end D5.S3.Arith.PrimitiveRoot.SieveSevenFactors

-- The utility header grammar requires its metadata on one physical line.
set_option linter.style.longLine.maxLineLength 237
