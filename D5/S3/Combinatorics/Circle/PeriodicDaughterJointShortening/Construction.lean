/- GID: D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Construction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Construction
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic minus-one physical joint transport with periodic daughter. -/
import D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.Words

/-! MINUS-one transport at K=(d+1)*r-1 with both full actual
OriginalOrder predicates. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

/- The linear sum and prefix-to-strip helpers are ports of the private
PeriodicShortening helpers at 447f4235385fe941888b620340cd4429dfbf0e61.
The remaining list identities organize native source prefixes. -/
private theorem sum_linear {α : Type*} (l : List α) (f g : α → ℤ) (u v : ℤ) :
    (l.map (fun x => u * f x + v * g x)).sum =
      u * (l.map f).sum + v * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_double {α : Type*} (l : List α) (f g b : α → ℤ) (u : ℤ)
    (hf : ∀ x, 2 * f x = u * g x + b x) :
    2 * (l.map f).sum = u * (l.map g).sum + (l.map b).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination hf x + ih

private theorem prefix_nonneg_le {α : Type*} (l : List α) (f : α → ℤ)
    (hf : ∀ x ∈ l, 0 ≤ f x) (h : ℕ) :
    0 ≤ ((l.take h).map f).sum ∧ ((l.take h).map f).sum ≤ (l.map f).sum := by
  have ht : 0 ≤ ((l.take h).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_take hx)
  have hd : 0 ≤ ((l.drop h).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_drop hx)
  have he := congrArg (fun xs : List α => (xs.map f).sum) (List.take_append_drop h l)
  simp only [List.map_append, List.sum_append] at he
  exact ⟨ht, by omega⟩

private theorem strip_of_prefix {α : Type*} (f : α → ℤ) (B h : ℤ) (l : List α)
    (hl : ∀ t, 0 ≤ h + ((l.take t).map f).sum ∧
      h + ((l.take t).map f).sum ≤ B) : InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using hl 0
  | cons x xs ih =>
      refine ⟨by simpa using (hl 0).1, by simpa using (hl 0).2, ih (h + f x) ?_⟩
      intro t
      simpa [List.take_succ_cons, add_assoc] using hl (t + 1)

private theorem sum_of_perm {k : ℕ} (l : List (Fin k))
    (hp : l.Perm (List.finRange k)) (f : Fin k → ℤ) :
    (l.map f).sum = ∑ i : Fin k, f i := by
  rw [(hp.map f).sum_eq]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

private theorem regular_block (d w r : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r)
    (eta : List (Fin (d + 1))) (heta : OriginalOrder (d + 1) (2 * w) eta)
    (j : Fin (r - 1)) :
    let f := actualSource (length d r) (seed d w r)
    InStrip f (N d r / 2) ((w : ℤ) * (geom (d + 1) j.val : ℤ))
        (eta.map (regularLabel d r hr j)) ∧
      ((eta.map (regularLabel d r hr j)).map f).sum = (w : ℤ) * q d ^ j.val := by
  dsimp only
  let f := actualSource (length d r) (seed d w r)
  have fs := scale_facts d w r hd hw hr
  have hv (i : Fin (d + 1)) : f (regularLabel d r hr j i) = regularValue d w r j.val i :=
    regular_source d w r j.val hd hw hr j.isLt i (regularLabel d r hr j i).isLt
  have hdef := defect_data d w j.val hd hw
  have htotal : (eta.map (defect d w j.val)).sum = 2 * w * q d ^ j.val := by
    rw [sum_of_perm eta heta.1]; exact hdef.2
  have hbeta : (eta.map (beta d w)).sum = 0 := heta.2.1
  have hgeo : (geom (d + 1) j.val : ℤ) + q d ^ j.val ≤ H d r := by
    have he := geom_succ (d + 1) j.val (by omega)
    have hm := geom_mono (d + 1) (by omega) (show j.val + 1 ≤ r - 1 by omega)
    change (geom (d + 1) (j.val + 1) : ℤ) ≤ H d r at hm
    simpa only [he, q] using hm
  have hg0 : 0 ≤ G d r := by linarith [fs.G_ge, fs.q_ge]
  constructor
  · apply strip_of_prefix f _ _ _
    intro h
    rw [← List.map_take]
    simp only [List.map_map, Function.comp_def]
    simp_rw [hv]
    have he := sum_double (eta.take h) (regularValue d w r j.val)
      (beta d w) (defect d w j.val) (G d r) (regular_double d w r j.val hd hw hr)
    have hb := heta.2.2 h
    change 0 ≤ ((eta.take h).map (beta d w)).sum ∧
      ((eta.take h).map (beta d w)).sum ≤ modulus (d + 1) / 2 at hb
    rw [fs.daughter_half] at hb
    have hdft := prefix_nonneg_le eta (defect d w j.val) (fun i _ => hdef.1 i) h
    rw [htotal] at hdft
    have hin : 0 ≤ (w : ℤ) * (geom (d + 1) j.val : ℤ) := by positivity
    have hb0 := mul_nonneg hg0 hb.1
    have hb1 := mul_le_mul_of_nonneg_left hb.2 hg0
    have hg1 := mul_le_mul_of_nonneg_left hgeo (show 0 ≤ 2 * (w : ℤ) by positivity)
    constructor <;> nlinarith only [he, hdft.1, hdft.2, hin, hb0, hb1, hg1,
      fs.regular_margin, fs.old_half]
  · have hmap : f ∘ regularLabel d r hr j = regularValue d w r j.val := by
      funext i
      exact hv i
    rw [List.map_map, hmap]
    have he := sum_double eta (regularValue d w r j.val) (beta d w)
      (defect d w j.val) (G d r) (regular_double d w r j.val hd hw hr)
    rw [htotal, hbeta] at he
    nlinarith only [he]

private theorem lower_blocks (d w r : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r)
    (eta : List (Fin (d + 1))) (heta : OriginalOrder (d + 1) (2 * w) eta) :
    let f := actualSource (length d r) (seed d w r)
    InStrip f (N d r / 2) 0 (lowerWord d r hr eta) ∧
      ((lowerWord d r hr eta).map f).sum = (w : ℤ) * H d r := by
  dsimp only
  let f := actualSource (length d r) (seed d w r)
  have fs := scale_facts d w r hd hw hr
  have hcap : 0 ≤ N d r / 2 := by
    have := (TwoRunSource.modulus_positive_odd (length d r) (by
      have := fs.length_succ; have := Nat.mul_le_mul (show 3 ≤ d + 1 by omega) hr; omega)).1
    change 0 < N d r at this; omega
  have hchain (s : ℕ) (hs : s ≤ r - 1) :
      let word := (List.finRange s).flatMap (fun j =>
        eta.map (regularLabel d r hr ⟨j.val, by omega⟩))
      InStrip f (N d r / 2) 0 word ∧
        (word.map f).sum = (w : ℤ) * (geom (d + 1) s : ℤ) := by
    revert hs
    induction s with
    | zero =>
        intro hs
        simp [InStrip, geom, hcap]
    | succ s ih =>
        intro hs
        have hi := ih (by omega)
        have hb := regular_block d w r hd hw hr eta heta (⟨s, by omega⟩ : Fin (r - 1))
        have hg := geom_succ (d + 1) s (by omega)
        dsimp only at hi hb ⊢
        rw [List.finRange_succ_last]
        simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]
        constructor
        · apply inStrip_append hi.1
          simpa only [hi.2, zero_add] using hb.1
        · simp only [List.map_append, List.sum_append]
          rw [hi.2, hb.2, hg]
          change (w : ℤ) * (geom (d + 1) s : ℤ) + w * q d ^ s =
            w * ((geom (d + 1) s : ℤ) + q d ^ s)
          ring
  simpa only [lowerWord, H] using hchain (r - 1) (by omega)

private theorem top_block (d w r cut : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hcut : cut ≤ d)
    (tau : List (Fin d)) (hold : OriginalOrder d w tau)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d tau cut)) :
    let f := actualSource (length d r) (seed d w r)
    InStrip f (N d r / 2) ((w : ℤ) * H d r) (tau.map (topLabel d r hr)) ∧
      ((tau.map (topLabel d r hr)).map f).sum = -(w : ℤ) * H d r := by
  dsimp only
  let f := actualSource (length d r) (seed d w r)
  have fs := scale_facts d w r hd hw hr
  have htau : tau.length = d := by simpa using hold.1.length_eq
  have hc : cut ≤ tau.length := by omega
  have hv (i : Fin d) : f (topLabel d r hr i) = topValue d w r i :=
    top_source d w r hd hw hr i (topLabel d r hr i).isLt
  let b := fun i : Fin d => beta d w i.castSucc
  have hbtotal : (tau.map b).sum = -(w : ℤ) := by
    have he := ear_sum d tau cut (beta d w)
    have hz : ((earWord d tau cut).map (beta d w)).sum = 0 := hnew.2.1
    rw [hz, phase_fresh d w hd hw] at he
    change 0 = (tau.map b).sum + w at he
    omega
  have hbeta_prefix (h : ℕ) : -(w : ℤ) ≤ ((tau.take h).map b).sum ∧
      ((tau.take h).map b).sum ≤ n d := by
    by_cases hh : h ≤ cut
    · have he := ear_prefix_sum d tau cut hc (beta d w) h
      have hb := hnew.2.2 h
      change 0 ≤ (((earWord d tau cut).take h).map (beta d w)).sum ∧
        (((earWord d tau cut).take h).map (beta d w)).sum ≤ modulus (d + 1) / 2 at hb
      simp only [ite_eq_left hh, add_zero] at he
      rw [he, fs.daughter_half] at hb
      change 0 ≤ ((tau.take h).map b).sum ∧ ((tau.take h).map b).sum ≤ n d at hb
      exact ⟨by linarith [fs.w_nonneg], hb.2⟩
    · have hh' : ¬ h + 1 ≤ cut := by omega
      have he := ear_prefix_sum d tau cut hc (beta d w) (h + 1)
      have hb := hnew.2.2 (h + 1)
      change 0 ≤ (((earWord d tau cut).take (h + 1)).map (beta d w)).sum ∧
        (((earWord d tau cut).take (h + 1)).map (beta d w)).sum ≤
          modulus (d + 1) / 2 at hb
      simp only [ite_eq_right hh', Nat.add_sub_cancel, phase_fresh d w hd hw] at he
      rw [he, fs.daughter_half] at hb
      change 0 ≤ ((tau.take h).map b).sum + w ∧
        ((tau.take h).map b).sum + w ≤ n d at hb
      constructor <;> linarith [fs.w_nonneg]
  have hH0 : 0 ≤ H d r := by linarith [fs.H_ge]
  have hR0 : 0 ≤ R d r := by linarith [fs.R_ge]
  have hprefix (h : ℕ) :
      ((tau.take h).map (topValue d w r)).sum =
        R d r * ((tau.take h).map (actualSource d w)).sum +
          H d r * ((tau.take h).map b).sum := by
    exact sum_linear (tau.take h) (actualSource d w) b (R d r) (H d r)
  constructor
  · apply strip_of_prefix f _ _ _
    intro h
    rw [← List.map_take]
    simp only [List.map_map, Function.comp_def]
    simp_rw [hv]
    rw [hprefix]
    have ha := hold.2.2 h
    have hb := hbeta_prefix h
    have ha0 := mul_nonneg hR0 ha.1
    have ha1 := mul_le_mul_of_nonneg_left ha.2 hR0
    have hb0 := mul_le_mul_of_nonneg_left hb.1 hH0
    have hb1 := mul_le_mul_of_nonneg_left hb.2 hH0
    have hhalfR := congrArg (fun z : ℤ => R d r * z) fs.base_half
    constructor <;> nlinarith only [ha0, ha1, hb0, hb1, hhalfR, fs.top_margin, fs.old_half]
  · have hmap : f ∘ topLabel d r hr = topValue d w r := by
      funext i
      exact hv i
    rw [List.map_map, hmap]
    have he := sum_linear tau (actualSource d w) b (R d r) (H d r)
    change (tau.map (topValue d w r)).sum = _ at he
    rw [he, hold.2.1, hbtotal]
    ring

private theorem daughter_order (d w r : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r)
    (eta : List (Fin (d + 1))) (heta : OriginalOrder (d + 1) (2 * w) eta) :
    OriginalOrder (length d r + 1) (2 * seed d w r) (daughterWord d r hr eta) := by
  let f := actualSource (length d r + 1) (2 * seed d w r)
  have fs := scale_facts d w r hd hw hr
  have hg0 : 0 ≤ G d r := by linarith [fs.G_ge, fs.q_ge]
  have hblock (j : Fin r) :
      InStrip f (modulus (length d r + 1) / 2) 0 (eta.map (daughterLabel d r hr j)) ∧
      ((eta.map (daughterLabel d r hr j)).map f).sum = 0 := by
    have hv (i : Fin (d + 1)) : f (daughterLabel d r hr j i) = G d r * beta d w i :=
      daughter_source d w r j.val hd hw hr i (daughterLabel d r hr j i).isLt
    have hsum (xs : List (Fin (d + 1))) :
        ((xs.map (daughterLabel d r hr j)).map f).sum = G d r * (xs.map (beta d w)).sum := by
      simp only [List.map_map, Function.comp_def]
      simp_rw [hv]
      have he := sum_linear xs (beta d w) (fun _ => 0) (G d r) 0
      simpa using he
    constructor
    · apply strip_of_prefix f _ 0 _
      intro h
      rw [← List.map_take, hsum]
      have hb := heta.2.2 h
      change 0 ≤ ((eta.take h).map (beta d w)).sum ∧
        ((eta.take h).map (beta d w)).sum ≤ modulus (d + 1) / 2 at hb
      rw [fs.daughter_half] at hb
      constructor
      · simpa using mul_nonneg hg0 hb.1
      · have hh := mul_le_mul_of_nonneg_left hb.2 hg0
        simpa using hh.trans fs.daughter_margin
    · have hz : (eta.map (beta d w)).sum = 0 := heta.2.1
      rw [hsum, hz, mul_zero]
  have hall (js : List (Fin r)) :
      InStrip f (modulus (length d r + 1) / 2) 0
          (js.flatMap (fun j => eta.map (daughterLabel d r hr j))) ∧
      ((js.flatMap (fun j => eta.map (daughterLabel d r hr j))).map f).sum = 0 := by
    induction js with
    | nil =>
        have hp := (TwoRunSource.modulus_positive_odd (length d r + 1) (by omega)).1
        simp only [List.flatMap_nil, List.map_nil, List.sum_nil, InStrip]
        exact ⟨⟨by omega, by omega⟩, trivial⟩
    | cons j js ih =>
        simp only [List.flatMap_cons]
        constructor
        · apply inStrip_append (hblock j).1
          simpa only [(hblock j).2, zero_add] using ih.1
        · simp only [List.map_append, List.sum_append, (hblock j).2, ih.2, zero_add]
  have hh := hall (List.finRange r)
  refine ⟨daughter_perm d r hr eta heta.1, hh.2, ?_⟩
  intro h
  simpa only [daughterWord, zero_add, Set.mem_Icc, f] using inStrip_prefix hh.1 h

/-- Ascending full daughter blocks followed by the shortened top OLD block.
The common cut inserts exactly the globally fresh label. All natural prefixes
and both zero totals are part of the two actual OriginalOrder conclusions. -/
public theorem periodic_daughter_joint_shortening
    (d w r cut : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hcut : cut ≤ d)
    (tau : List (Fin d))
    (hold : OriginalOrder d w tau)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d tau cut)) :
    commonCut d r cut ≤ length d r ∧
    OriginalOrder (length d r) (seed d w r) (shortenedWord d r hr tau cut) ∧
    OriginalOrder (length d r + 1) (2 * seed d w r)
      (earWord (length d r) (shortenedWord d r hr tau cut) (commonCut d r cut)) := by
  have hc : commonCut d r cut ≤ length d r := by
    rw [length_split d r hr]; dsimp [commonCut]; omega
  have hlo := lower_blocks d w r hd hw hr (earWord d tau cut) hnew
  have htop := top_block d w r cut hd hw hr hcut tau hold hnew
  have hstrip : InStrip (actualSource (length d r) (seed d w r)) (N d r / 2) 0
      (shortenedWord d r hr tau cut) := by
    unfold shortenedWord
    apply inStrip_append hlo.1
    simpa only [hlo.2, zero_add] using htop.1
  have hsum : ((shortenedWord d r hr tau cut).map
      (actualSource (length d r) (seed d w r))).sum = 0 := by
    simp only [shortenedWord, List.map_append, List.sum_append, hlo.2, htop.2]
    ring
  refine ⟨hc, ⟨shortened_perm d r cut hr tau hold.1, hsum, ?_⟩, ?_⟩
  · intro h
    simpa only [N, zero_add, Set.mem_Icc] using inStrip_prefix hstrip h
  · rw [literal_ear d r cut hr tau hold.1]
    exact daughter_order d w r hd hw hr _ hnew

end D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
