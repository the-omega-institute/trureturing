/- GID: D5/S3/Combinatorics/Circle/NativeSeedChains
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/NativeSeedChains
   mirror-E: none(waiver:audit-open-22063)
   anchors: [D5/S3/Combinatorics/Circle/SourceWidth, D5/S3/Combinatorics/Circle/ExpandingSourcePath]
   utility: none
   digest: Native positive-SMALL sources have physical dyadic chains with exact seed transport. -/
module
public import D5.S3.Combinatorics.Circle.ExpandingSourcePath

/-! # Physical dyadic chains in native positive-SMALL sources -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.NativeSeedChains
open SourceWidth ExpandingSourcePath

private theorem geometry {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i) :
    (∀ i, actualSource k t i ≠ 0) ∧
    (∀ i, 0 < actualSource k t i → 3 * actualSource k t i ≤ modulus k) ∧
    (∀ i, actualSource k t i < 0 →
      quarter k ≤ -actualSource k t i ∧
      actualSource k t (phase (by omega) i 1) = 2 * actualSource k t i + modulus k ∧
      0 < actualSource k t (phase (by omega) i 1)) := by
  classical
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  let w := actualSource k t
  let σ := fun i : Fin k => phase (by omega : 0 < k) i 1
  have hb (i : Fin k) : -(2 * quarter k - 1) ≤ w i ∧ w i ≤ 2 * quarter k - 1 := by
    have h := centered_bounds hNpos hodd ((2 : ℤ) ^ i.val * t)
    change -half k ≤ w i ∧ w i ≤ half k at h
    rwa [hC] at h
  have hs (i : Fin k) : w (σ i) = doubleStep (modulus k) (w i) := by
    simpa [w, σ] using phase_step hk t i 0
  have hnz (i : Fin k) : w i ≠ 0 := by
    intro h
    have hh := hsmall i (by change |w i| < quarter k; rw [h]; norm_num; omega)
    change 0 < w i at hh
    omega
  have neg (i : Fin k) (hi : w i < 0) :
      quarter k ≤ -w i ∧ w (σ i) = 2 * w i + modulus k ∧ 0 < w (σ i) := by
    have hl : quarter k ≤ -w i := by
      by_contra hh
      have hp := hsmall i (by change |w i| < quarter k; rw [abs_of_neg hi]; omega)
      change 0 < w i at hp
      omega
    have ht := hs i
    rw [doubleStep, ite_eq_right (by omega : ¬modulus k < 4 * w i),
      ite_eq_left (by omega : 4 * w i < -modulus k)] at ht
    have hbi := hb i
    exact ⟨hl, ht, by omega⟩
  have posStep (i : Fin k) (hi : quarter k ≤ w i) :
      w (σ i) = 2 * w i - modulus k ∧ w (σ i) < 0 ∧
      w (σ (σ i)) = 4 * w i - modulus k ∧ 0 < w (σ (σ i)) := by
    have ht := hs i
    rw [doubleStep, ite_eq_left (by omega : modulus k < 4 * w i)] at ht
    have hbi := hb i
    have hneg : w (σ i) < 0 := by omega
    obtain ⟨_, ht2, hp2⟩ := neg (σ i) hneg
    exact ⟨ht, hneg, by omega, hp2⟩
  have existsPos : ∃ i, 0 < w i := by
    let i : Fin k := ⟨0, by omega⟩
    by_cases hi : 0 < w i
    · exact ⟨i, hi⟩
    · exact ⟨σ i, (neg i (by have := hnz i; omega)).2.2⟩
  let P := Finset.univ.filter (fun i : Fin k => 0 < w i)
  have memP (i : Fin k) : i ∈ P ↔ 0 < w i := by simp [P]
  obtain ⟨i, hi⟩ := existsPos
  obtain ⟨a, ha, hmax⟩ := P.exists_max_image w ⟨i, (memP i).2 hi⟩
  have hapos := (memP a).1 ha
  have haLarge : quarter k ≤ w a := by
    by_contra hh
    have ht := hs a
    rw [doubleStep, ite_eq_right (by omega : ¬modulus k < 4 * w a),
      ite_eq_right (by omega : ¬4 * w a < -modulus k)] at ht
    have hm := hmax (σ a) ((memP _).2 (by omega))
    omega
  obtain ⟨_, _, ht, hp⟩ := posStep a haLarge
  have hm := hmax (σ (σ a)) ((memP _).2 hp)
  refine ⟨hnz, ?_, neg⟩
  intro j hj
  have hmj := hmax j ((memP _).2 hj)
  change 3 * w j ≤ modulus k
  omega

private theorem phase_add {k : ℕ} (hk : 0 < k) (a : Fin k) (i j : ℕ) :
    phase hk (phase hk a i) j = phase hk a (i + j) := by
  apply Fin.ext
  simp only [phase]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem path_nodup {k : ℕ} (hk : 0 < k) (a : Fin k) (m : ℕ)
    (hm : m ≤ k) : (path hk a m).Nodup := by
  unfold path
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj he
  have hi' : i < k := lt_of_lt_of_le (List.mem_range.mp hi) hm
  have hj' : j < k := lt_of_lt_of_le (List.mem_range.mp hj) hm
  have hh : Nat.ModEq k (a.val + i) (a.val + j) := congrArg Fin.val he
  have hc := Nat.ModEq.add_left_cancel' a.val hh
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using hc

private theorem first_root {k t : ℕ} (hk : 3 ≤ k)
    (a : Fin k) (ha : 0 < actualSource k t a) :
    ∃ r : ℕ, quarter k ≤ actualSource k t (phase (by omega) a r) ∧
      (∀ j < r, 0 < actualSource k t (phase (by omega) a j) ∧
        actualSource k t (phase (by omega) a j) < quarter k) ∧
      (∀ j ≤ r, actualSource k t (phase (by omega) a j) =
        (2 : ℤ) ^ j * actualSource k t a) := by
  obtain ⟨hQ, hN, _, _, _⟩ := source_geometry hk
  have aux : ∀ n : ℕ, ∀ a : Fin k,
      (quarter k - actualSource k t a).toNat = n → 0 < actualSource k t a →
      ∃ r : ℕ, quarter k ≤ actualSource k t (phase (by omega) a r) ∧
        (∀ j < r, 0 < actualSource k t (phase (by omega) a j) ∧
          actualSource k t (phase (by omega) a j) < quarter k) ∧
        (∀ j ≤ r, actualSource k t (phase (by omega) a j) =
          (2 : ℤ) ^ j * actualSource k t a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a hn ha
      by_cases hl : quarter k ≤ actualSource k t a
      · refine ⟨0, by simpa using hl, by omega, ?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp
      · have hstep : actualSource k t (phase (by omega) a 1) = 2 * actualSource k t a := by
          have ht := phase_step hk t a 0
          simp only [phase_zero, zero_add] at ht
          rw [doubleStep, ite_eq_right (by omega), ite_eq_right (by omega)] at ht
          exact ht
        let b := phase (by omega : 0 < k) a 1
        have hb : 0 < actualSource k t b := by dsimp [b]; omega
        have hm : (quarter k - actualSource k t b).toNat < n := by
          dsimp [b]
          rw [hstep]
          omega
        obtain ⟨r, hr, hpre, hpow⟩ := ih _ hm b rfl hb
        have hshift (j : ℕ) : phase (by omega) b j = phase (by omega) a (j + 1) := by
          dsimp [b]
          rw [phase_add]
          congr 1 <;> omega
        refine ⟨r + 1, ?_, ?_, ?_⟩
        · simpa [hshift] using hr
        · intro j hj
          cases j with
          | zero => simpa using And.intro ha (lt_of_not_ge hl)
          | succ j => simpa [hshift] using hpre j (by omega)
        · intro j hj
          cases j with
          | zero => simp
          | succ j =>
            have ht := hpow j (by omega)
            rw [hshift] at ht
            rw [ht, show actualSource k t b = 2 * actualSource k t a from hstep, pow_succ]
            ring
  exact aux _ a rfl ha

/-- Every native negative label starts a finite physical dyadic chain. The SMALL
list is the literal forward path; its root and following negative are not
selected by their numerical values. -/
theorem native_chain_extraction {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i)
    (n : Fin k) (hn : actualSource k t n < 0) :
    let a := phase (by omega) n 1
    ∃ r : ℕ,
      let root := phase (by omega) a r
      let neg := phase (by omega) a (r + 1)
      let next := phase (by omega) a (r + 2)
      let s := path (by omega) a r
      r + 2 ≤ k ∧ (s ++ [root, neg]).Nodup ∧
      0 < actualSource k t a ∧ actualSource k t a % 4 = 1 ∧
      (∀ j < r, 0 < actualSource k t (phase (by omega) a j) ∧
        actualSource k t (phase (by omega) a j) < quarter k) ∧
      Dyadic (actualSource k t) (actualSource k t a) s ∧
      actualSource k t root = (2 : ℤ) ^ r * actualSource k t a ∧
      quarter k ≤ actualSource k t root ∧ 3 * actualSource k t root ≤ modulus k ∧
      actualSource k t neg = 2 * actualSource k t root - modulus k ∧
      actualSource k t neg < 0 ∧
      actualSource k t next = 4 * actualSource k t root - modulus k ∧
      0 < actualSource k t next ∧ actualSource k t next % 4 = 1 ∧
      (s.map (actualSource k t)).sum = actualSource k t root - actualSource k t a ∧
      0 ≤ -actualSource k t neg - actualSource k t root ∧
      (s.map (actualSource k t)).sum -
        (-actualSource k t neg - actualSource k t root) =
          actualSource k t next - actualSource k t a := by
  dsimp only
  obtain ⟨hnz, hupper, hneg⟩ := geometry hk hsmall
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  let a := phase (by omega : 0 < k) n 1
  have ha := (hneg n hn).2.2
  change 0 < actualSource k t a at ha
  obtain ⟨r, hr, hpre, hpow⟩ := first_root hk a ha
  let root := phase (by omega : 0 < k) a r
  let neg := phase (by omega : 0 < k) a (r + 1)
  let next := phase (by omega : 0 < k) a (r + 2)
  have hback : phase (by omega) a (k - 1) = n := by
    dsimp [a]
    rw [phase_add]
    apply Fin.ext
    simp [phase, show 1 + (k - 1) = k by omega, Nat.mod_eq_of_lt n.isLt]
  have hlen : r + 2 ≤ k := by
    by_contra hh
    have ht := hpow (k - 1) (by omega)
    rw [hback] at ht
    have hp : 0 < (2 : ℤ) ^ (k - 1) := pow_pos (by norm_num) _
    nlinarith [mul_pos hp ha]
  have hinv : path (by omega) a r ++ [root, neg] = path (by omega) a (r + 2) := by
    unfold path
    rw [List.range_add, List.map_append]
    norm_num [List.range_succ, List.map_map, Function.comp_def, root, neg]
  have hnodup : (path (by omega) a r ++ [root, neg]).Nodup := by
    rw [hinv]
    exact path_nodup (by omega) a (r + 2) hlen
  have hroot : quarter k ≤ actualSource k t root := hr
  have hrootpos : 0 < actualSource k t root := by omega
  have hu := hupper root hrootpos
  have hb := centered_bounds hNpos hodd ((2 : ℤ) ^ root.val * t)
  change -half k ≤ actualSource k t root ∧ actualSource k t root ≤ half k at hb
  rw [hC] at hb
  have hrootstep : actualSource k t neg = 2 * actualSource k t root - modulus k := by
    have ht := phase_step hk t a r
    change actualSource k t neg = doubleStep (modulus k) (actualSource k t root) at ht
    rw [doubleStep, ite_eq_left (by omega)] at ht
    exact ht
  have hnegval : actualSource k t neg < 0 := by omega
  have hnextstep : actualSource k t next = 4 * actualSource k t root - modulus k := by
    have ht := (hneg neg hnegval).2.1
    have he : phase (by omega) neg 1 = next := by
      dsimp [neg, next]
      rw [phase_add]
    rw [he, hrootstep] at ht
    omega
  have hnextpos : 0 < actualSource k t next := by
    have ht := (hneg neg hnegval).2.2
    have he : phase (by omega) neg 1 = next := by dsimp [neg, next]; rw [phase_add]
    rwa [he] at ht
  have hseedmod : actualSource k t a % 4 = 1 := by
    let pred : Fin k := ⟨(n.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
    have he : phase (by omega) pred 1 = n := by
      apply Fin.ext
      dsimp [phase, pred]
      rw [Nat.mod_add_mod]
      have hh : n.val + k - 1 + 1 = n.val + k := by omega
      rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt n.isLt]
    have hpredpos : 0 < actualSource k t pred := by
      by_contra hh
      have hz := hnz pred
      have hp := (hneg pred (by omega)).2.2
      rw [he] at hp
      omega
    have hp : quarter k ≤ actualSource k t pred := by
      have hbpred := centered_bounds hNpos hodd ((2 : ℤ) ^ pred.val * t)
      change -half k ≤ actualSource k t pred ∧ actualSource k t pred ≤ half k at hbpred
      rw [hC] at hbpred
      have ht := phase_step hk t pred 0
      simp only [phase_zero, zero_add, he] at ht
      unfold doubleStep at ht
      split_ifs at ht <;> omega
    have hpn : actualSource k t n = 2 * actualSource k t pred - modulus k := by
      have ht := phase_step hk t pred 0
      simp only [phase_zero, zero_add, he] at ht
      rw [doubleStep, ite_eq_left (by omega)] at ht
      exact ht
    have hna := (hneg n hn).2.1
    change actualSource k t a = 2 * actualSource k t n + modulus k at hna
    omega
  have hdyadic : Dyadic (actualSource k t) (actualSource k t a) (path (by omega) a r) := by
    have aux : ∀ j m : ℕ, j + m ≤ r →
        Dyadic (actualSource k t) ((2 : ℤ) ^ j * actualSource k t a)
          ((List.range m).map (fun i => phase (by omega) a (j + i))) := by
      intro j m
      induction m generalizing j with
      | zero => intro _; trivial
      | succ m ih =>
        intro hj
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
        refine ⟨hpow j (by omega), ?_⟩
        have ht := ih (j + 1) (by omega)
        convert ht using 1
        · rw [pow_succ]; ring
        · congr 1
          funext i
          congr 1
          omega
    simpa [path] using aux 0 r (by omega)
  have hsum := dyadic_sum hdyadic
  have hrootpow := hpow r (le_refl _)
  change actualSource k t root = (2 : ℤ) ^ r * actualSource k t a at hrootpow
  have hmass : ((path (by omega) a r).map (actualSource k t)).sum =
      actualSource k t root - actualSource k t a := by
    rw [path_length] at hsum
    rw [hsum, hrootpow]
    ring
  have hnextmod : actualSource k t next % 4 = 1 := by omega
  have hdebt : 0 ≤ -actualSource k t neg - actualSource k t root := by omega
  have htransport : ((path (by omega) a r).map (actualSource k t)).sum -
      (-actualSource k t neg - actualSource k t root) =
        actualSource k t next - actualSource k t a := by omega
  exact ⟨r, hlen, hnodup, ha, hseedmod, hpre, hdyadic, hrootpow, hroot, hu,
    hrootstep, hnegval, hnextstep, hnextpos, hnextmod, hmass, hdebt, htransport⟩

end D5.S3.Combinatorics.Circle.NativeSeedChains
