/- GID: D5/S3/Combinatorics/Circle/ThreeParentFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeParentFamily
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: A sharp infinite actual-source family via binary child selection and a closed strip path. -/
import D5.S3.Combinatorics.Circle.SourceWidth

/-! A complete physical-label construction for one infinite family of centered sources. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeParentFamily
open SourceWidth

private theorem source_values (r : ℕ) (hr : 4 ≤ r) :
    let U : ℤ := 2 ^ (r - 1)
    let f := actualSource (r + 4) (11 * 2 ^ (r - 1) - 1)
    f ⟨0, by omega⟩ = 11 * U - 1 ∧
    f ⟨1, by omega⟩ = -10 * U - 1 ∧
    f ⟨2, by omega⟩ = 12 * U - 3 ∧
    f ⟨3, by omega⟩ = -8 * U - 5 ∧
    f ⟨4, by omega⟩ = 16 * U - 11 ∧
    ∀ j (hj : j < r - 1), f ⟨j + 5, by omega⟩ = -21 * 2 ^ j := by
  let U : ℤ := 2 ^ (r - 1)
  have hU : 8 ≤ U := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 3 ≤ r - 1 by omega)
    norm_num at h
    exact h
  have hN : modulus (r + 4) = 32 * U - 1 := by
    dsimp [modulus, U]
    rw [show r + 4 = (r - 1) + 5 by omega, pow_add]
    norm_num
    ring
  have ht : ((11 * 2 ^ (r - 1) - 1 : ℕ) : ℤ) = 11 * U - 1 := by
    have hh : 1 ≤ (11 * 2 ^ (r - 1) : ℕ) := by
      have hp : (0 : ℕ) < 2 ^ (r - 1) := by positivity
      omega
    rw [Nat.cast_sub hh]
    simp [U]
  let v : ℕ → ℤ := fun i => centered (modulus (r + 4))
    (2 ^ i * (11 * U - 1))
  have step (i : ℕ) : v (i + 1) = doubleStep (32 * U - 1) (v i) := by
    dsimp [v]
    rw [show (2 : ℤ) ^ (i + 1) * (11 * U - 1) =
        2 * (2 ^ i * (11 * U - 1)) by rw [pow_succ]; ring,
      centered_double (by rw [hN]; omega) (by rw [hN]; omega), hN]
  have hv0 : v 0 = 11 * U - 1 := by
    have hh : (32 * U - 1) / 2 = 16 * U - 1 := by omega
    dsimp [v]
    rw [hN, centered, hh]
    norm_num only [pow_zero, one_mul]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have hv1 : v 1 = -10 * U - 1 := by
    rw [show 1 = 0 + 1 by rfl, step, hv0, doubleStep, ite_eq_left (by omega)]
    ring
  have hv2 : v 2 = 12 * U - 3 := by
    rw [show 2 = 1 + 1 by rfl, step, hv1, doubleStep, ite_eq_right (by omega), ite_eq_left (by omega)]
    ring
  have hv3 : v 3 = -8 * U - 5 := by
    rw [show 3 = 2 + 1 by rfl, step, hv2, doubleStep, ite_eq_left (by omega)]
    ring
  have hv4 : v 4 = 16 * U - 11 := by
    rw [show 4 = 3 + 1 by rfl, step, hv3, doubleStep, ite_eq_right (by omega), ite_eq_left (by omega)]
    ring
  have hv5 : v 5 = -21 := by
    rw [show 5 = 4 + 1 by rfl, step, hv4, doubleStep, ite_eq_left (by omega)]
    ring
  have tail (j : ℕ) (hj : j < r - 1) : v (j + 5) = -21 * 2 ^ j := by
    induction j with
    | zero => simpa using hv5
    | succ j ih =>
      have ih' := ih (by omega)
      have hp : 4 * (2 : ℤ) ^ j ≤ U := by
        have h := (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2)
          (show j + 2 ≤ r - 1 by omega))
        simpa [U, pow_add, mul_comm] using h
      have hp0 : 0 < (2 : ℤ) ^ j := by positivity
      rw [show j + 1 + 5 = (j + 5) + 1 by omega, step, ih', doubleStep,
        ite_eq_right (by nlinarith), ite_eq_right (by nlinarith), pow_succ]
      ring
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  simp only [actualSource, ht]
  exact ⟨hv0, hv1, hv2, hv3, hv4, tail⟩

private theorem dyadic_ofFn {α : Type*} (f : α → ℤ) (n : ℕ) (b : ℤ)
    (g : Fin n → α) (hg : ∀ i, f (g i) = 2 ^ i.val * b) :
    SourceWidth.Dyadic f b (List.ofFn g) := by
  induction n generalizing b with
  | zero => simp [SourceWidth.Dyadic]
  | succ n ih =>
    rw [List.ofFn_succ]
    refine ⟨by simpa using hg 0, ?_⟩
    apply ih
    intro i
    rw [hg i.succ]
    simp only [Fin.val_succ, pow_succ]
    ring

private theorem family_schedule (r : ℕ) (hr : 4 ≤ r) :
    ∃ word : List (Fin (r + 4)), word.Perm (List.finRange (r + 4)) ∧
      InStrip (actualSource (r + 4) (11 * 2 ^ (r - 1) - 1))
        (16 * (2 : ℤ) ^ (r - 1) - 11) 0 word := by
  classical
  let U : ℤ := 2 ^ (r - 1)
  let f := actualSource (r + 4) (11 * 2 ^ (r - 1) - 1)
  let p (i : ℕ) (hi : i < r + 4) : Fin (r + 4) := ⟨i, hi⟩
  let a := p 0 (by omega)
  let b := p 1 (by omega)
  let c := p 2 (by omega)
  let d := p 3 (by omega)
  let e := p 4 (by omega)
  let g : Fin (r - 1) → Fin (r + 4) := fun j => ⟨j.val + 5, by omega⟩
  let children := List.ofFn g
  let H := 5 * U - 10
  let delta := (-H) % 21
  let P := 16 * U - 11
  have hU : 8 ≤ U := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 3 ≤ r - 1 by omega)
    norm_num at h
    exact h
  obtain ⟨ha, hb, hc, hd, he, htail⟩ := source_values r hr
  change f a = 11 * U - 1 at ha
  change f b = -10 * U - 1 at hb
  change f c = 12 * U - 3 at hc
  change f d = -8 * U - 5 at hd
  change f e = P at he
  change ∀ j (hj : j < r - 1), f ⟨j + 5, by omega⟩ = -21 * 2 ^ j at htail
  have hdyad : SourceWidth.Dyadic (fun x => -f x) 21 children := by
    apply dyadic_ofFn
    intro j
    dsimp [g]
    rw [htail j.val j.isLt]
    ring
  have hlen : children.length = r - 1 := by simp [children]
  have hsum : (children.map f).sum = -21 * (U - 1) := by
    have hh := dyadic_sum hdyad
    rw [sum_neg_map, hlen] at hh
    change -(children.map f).sum = (U - 1) * 21 at hh
    nlinarith
  have hdelta : 0 ≤ delta ∧ delta ≤ 20 := by
    dsimp [delta]
    have := Int.emod_nonneg (-H) (by norm_num : (21 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos (-H) (by norm_num : (0 : ℤ) < 21)
    omega
  have hpeak : 13 * U - 5 + delta ≤ P := by
    by_cases hr4 : r = 4
    · subst r
      norm_num [U, H, delta, P]
    · have hU16 : 16 ≤ U := by
        have h := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 4 ≤ r - 1 by omega)
        norm_num at h
        exact h
      dsimp [P]
      omega
  have hdiv : (H + delta) % 21 = 0 := by dsimp [delta]; omega
  let n : ℕ := ((H + delta) / 21).toNat
  have hn : (n : ℤ) * 21 = H + delta := by
    have h0 : 0 ≤ (H + delta) / 21 := Int.ediv_nonneg (by dsimp [H]; omega) (by norm_num)
    have hmod := Int.emod_add_mul_ediv (H + delta) 21
    dsimp [n]
    rw [Int.toNat_of_nonneg h0]
    omega
  have hnlt : n < 2 ^ children.length := by
    rw [hlen]
    have hh : (n : ℤ) < U := by dsimp [H] at hn; nlinarith
    dsimp [U] at hh
    exact_mod_cast hh
  obtain ⟨before, after, hperm, hbefore⟩ := dyadic_select hdyad n hnlt
  rw [sum_neg_map] at hbefore
  have hs_before : (before.map f).sum = -(H + delta) := by omega
  have hs_after : (after.map f).sum = delta - P := by
    have hh := (hperm.map f).sum_eq
    simp only [List.map_append, List.sum_append] at hh
    rw [hsum, hs_before] at hh
    dsimp [P, H]
    dsimp [H] at hh
    omega
  have hnonpos : ∀ x ∈ before ++ after, f x ≤ 0 := by
    intro x hx
    have hx' := hperm.mem_iff.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx'
    dsimp [g]
    rw [htail j.val j.isLt]
    have : 0 ≤ (2 : ℤ) ^ j.val := by positivity
    nlinarith
  have hbef : InStrip f P (H + delta) before := by
    apply inStrip_nonpos (fun x hx => hnonpos x (by simp [hx]))
    · dsimp [H, P]; omega
    · rw [hs_before]; omega
  have haft : InStrip f P P after := by
    apply inStrip_nonpos (fun x hx => hnonpos x (by simp [hx])) (le_refl _)
    rw [hs_after]
    omega
  have harcs : InStrip f P delta [a,b,c,d] := by
    simp only [InStrip, ha, hb, hc, hd]
    dsimp [H, P] at *
    omega
  have hclosed : InStrip f P 0 ([e] ++ after ++ [a,b,c,d] ++ before) := by
    simp only [List.append_assoc]
    apply inStrip_append (l := [e])
    · simp only [InStrip, he]; dsimp [P]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        he, zero_add, add_zero]
      apply inStrip_append (l := after) haft
      rw [hs_after]
      have hstart : P + (delta - P) = delta := by ring
      rw [hstart]
      apply inStrip_append (l := [a,b,c,d]) harcs
      have hend : delta + ([a,b,c,d].map f).sum = H + delta := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ha, hb, hc, hd]
        dsimp [H]; ring
      rw [hend]
      exact hbef
  have horig : [a,b,c,d,e] ++ children = List.finRange (r + 4) := by
    apply List.ext_getElem
    · simp [children]; omega
    · intro i hi hi'
      by_cases hi5 : i < 5
      · interval_cases i <;> simp [a,b,c,d,e,p]
      · have hj : i - 5 < r - 1 := by simp only [List.length_finRange] at hi'; omega
        rw [List.getElem_append_right (by simpa using (show 5 ≤ i by omega))]
        simp only [List.length_cons, List.length_nil]
        rw [List.getElem_ofFn]
        apply Fin.ext
        simp [g]
        omega
  refine ⟨[e] ++ after ++ [a,b,c,d] ++ before, ?_, hclosed⟩
  rw [← horig]
  have hp0 : ([e] ++ after ++ [a,b,c,d] ++ before).Perm
      ([a,b,c,d,e] ++ (before ++ after)) := by
    have hrot := (List.perm_append_comm :
      (([e] ++ after) ++ ([a,b,c,d] ++ before)).Perm
        (([a,b,c,d] ++ before) ++ ([e] ++ after)))
    have hmid : (before ++ e :: after).Perm (e :: (before ++ after)) := List.perm_middle
    apply List.Perm.trans (l₂ := [a,b,c,d] ++ (before ++ e :: after))
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hrot
    · simpa only [List.append_assoc, List.cons_append, List.nil_append]
        using hmid.append_left [a,b,c,d]
  exact hp0.trans (List.Perm.append_left _ hperm)

private theorem step_lower {α : Type*} (f : α → ℤ) (word : List α)
    (x : α) (hx : x ∈ word) (L B : ℤ)
    (hh : ∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc L B) : f x ≤ B - L := by
  obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp hx
  have hl := hh left.length
  have hr := hh (left.length + 1)
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil, List.map_append, List.sum_append] at hl
  have he : ((left ++ x :: right).take (left.length + 1)).map f =
      left.map f ++ [f x] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  rw [he] at hr
  simp only [List.sum_append, List.sum_singleton, Set.mem_Icc] at hr
  have hlo : L ≤ (left.map f).sum := hl.1
  omega

/-- Every physical label is scheduled once at the sharp width; any strip containing
all prefixes of any complete physical word has at least that width. -/
theorem sharp_actual_family (r : ℕ) (hr : 4 ≤ r) :
    let f := actualSource (r + 4) (11 * 2 ^ (r - 1) - 1)
    (∃ word : List (Fin (r + 4)), word.Nodup ∧ word.toFinset = Finset.univ ∧
      ∀ n : ℕ,
        ((word.take n).map f).sum ∈
          Set.Icc (0 : ℤ) (8 * 2 ^ r - 11) ∧
        ((word.take n).map f).sum ∈
          Set.Icc (0 : ℤ) (8 * 2 ^ r - 1)) ∧
    ∀ (word : List (Fin (r + 4))), word.toFinset = Finset.univ →
      ∀ L B : ℤ,
        (∀ n : ℕ,
          ((word.take n).map f).sum ∈
            Set.Icc L B) → 8 * (2 : ℤ) ^ r - 11 ≤ B - L := by
  have hpow : (2 : ℤ) ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ r by omega)]
  constructor
  · obtain ⟨word, hp, hs⟩ := family_schedule r hr
    refine ⟨word, hp.nodup_iff.mpr (List.nodup_finRange _), ?_, ?_⟩
    · apply Finset.eq_univ_of_forall
      intro x
      exact List.mem_toFinset.mpr (hp.mem_iff.mpr (List.mem_finRange x))
    · intro n
      have hh := inStrip_prefix hs n
      simp only [zero_add] at hh
      rw [hpow]
      constructor <;> constructor <;> omega
  · intro word hw L B hh
    let e : Fin (r + 4) := ⟨4, by omega⟩
    have he : e ∈ word := List.mem_toFinset.mp (by rw [hw]; simp)
    have hv := (source_values r hr).2.2.2.2.1
    have hs := step_lower _ word e he L B hh
    change actualSource (r + 4) (11 * 2 ^ (r - 1) - 1) e ≤ B - L at hs
    rw [show actualSource (r + 4) (11 * 2 ^ (r - 1) - 1) e =
      16 * (2 : ℤ) ^ (r - 1) - 11 from hv] at hs
    rw [hpow]
    omega

#print axioms sharp_actual_family
end D5.S3.Combinatorics.Circle.ThreeParentFamily
