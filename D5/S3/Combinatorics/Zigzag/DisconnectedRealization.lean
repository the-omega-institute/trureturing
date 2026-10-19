/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedRealization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Realizing absolute word colors on the actual residue-group vertices. -/

import D5.S3.Combinatorics.Zigzag.DisconnectedMarking
import D5.S3.Combinatorics.Zigzag.DisconnectedSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

private def supportRadius (n : Nat) (v : ZMod n) : Nat := min v.val (n-v.val)

private theorem radius_nat (n k : Nat) (hk : 1 ≤ k) (hkn : 2*k ≤ n) :
    supportRadius n (k : ZMod n) = k ∧ supportRadius n (-(k : ZMod n)) = k := by
  have hn : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hlt : k < n := by omega
  have hv : (k : ZMod n).val = k := ZMod.val_natCast_of_lt hlt
  have hz : (k : ZMod n) ≠ 0 := by
    intro h
    have he := congrArg ZMod.val h
    rw [hv] at he
    simp only [ZMod.val_zero] at he
    omega
  letI : NeZero (k : ZMod n) := ⟨hz⟩
  have hvn : (-(k : ZMod n)).val = n-k := by
    rw [ZMod.val_neg_of_ne_zero, hv]
  simp only [supportRadius, hv, hvn]
  constructor <;> omega

private def radialColor (n : Nat) (f : Nat → Bool) (v : ZMod n) : Bool :=
  if v = 1 then true else if v = -1 then false else f (supportRadius n v)

private theorem radial_roots (n : Nat) (hn : 3 ≤ n) (f : Nat → Bool) :
    radialColor n f 1 = true ∧ radialColor n f (-1) = false := by
  have hm : (-1 : ZMod n) ≠ 1 := by
    intro h
    have he := ZMod.neg_one_eq_one_iff.mp h
    omega
  simp [radialColor, hm]

private theorem radial_interior (n k : Nat) (hk : 2 ≤ k) (hkn : 2*k ≤ n)
    (f : Nat → Bool) :
    radialColor n f (k : ZMod n) = f k ∧
      radialColor n f (-(k : ZMod n)) = f k := by
  have hr := radius_nat n k (by omega) hkn
  have hone := radius_nat n 1 (by omega) (by omega)
  simp only [Nat.cast_one] at hone
  have hkp : (k : ZMod n) ≠ 1 := by
    intro h
    have he := congrArg (supportRadius n) h
    simp only [hr.1, Nat.cast_one, hone.1] at he
    omega
  have hkm : (k : ZMod n) ≠ -1 := by
    intro h
    have he := congrArg (supportRadius n) h
    simp only [hr.1, Nat.cast_one, hone.2] at he
    omega
  have hnp : -(k : ZMod n) ≠ 1 := by
    intro h
    have he := congrArg (supportRadius n) h
    simp only [hr.2, Nat.cast_one, hone.1] at he
    omega
  have hnm : -(k : ZMod n) ≠ -1 := by
    intro h
    have he := congrArg (supportRadius n) h
    simp only [hr.2, Nat.cast_one, hone.2] at he
    omega
  simp only [radialColor, if_neg hkp, if_neg hkm, if_neg hnp, if_neg hnm, hr.1, hr.2]
  exact ⟨True.intro, True.intro⟩

private def wordBand : (l : Nat) → Bool → (Fin l → Bool) → Nat → Bool
  | 0, b, _, _ => b
  | l+1, b, w, k => if k < 3 then b else wordBand l (w 0) (fun i => w i.succ) (k-3)

private theorem band_head (l : Nat) (b : Bool) (w : Fin l → Bool)
    (k : Nat) (hk : k < 3) : wordBand l b w k = b := by
  cases l <;> simp [wordBand, hk]

private theorem band_shift (l : Nat) (b : Bool) (w : Fin (l+1) → Bool)
    (j k : Nat) (hj : 1 ≤ j) (hk : j+2 ≤ k) :
    wordBand (l+1) b w (k-(j-1)) =
      wordBand l (w 0) (fun i => w i.succ) (k-(j+2)) := by
  have hge : ¬ k-(j-1) < 3 := by omega
  simp only [wordBand, if_neg hge]
  congr 1
  omega

private def uniformLow (a b : Bool) (f : Form) : Bool × Bool :=
  [(true,a), (b,a), (false,b), (a,b), (b,true), (a,false)].get f

private def uniformHigh (a b : Bool) (f : Form) : Bool × Bool :=
  [(true,b), (a,b), (false,a), (b,a), (a,true), (b,false)].get f

private theorem uniform_pair_colors (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n+1)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (low high : Form) (a b : Bool)
    (hold : color ((j-1 : Nat) : ZMod n) = a ∧ color (-((j-1 : Nat) : ZMod n)) = a)
    (hnew : color (j : ZMod n) = b ∧ color (-(j : ZMod n)) = b) :
    (color (formPair n j low).1 = color (formPair n j low).2 ∧
      color (formPair n (highClass n j) high).1 =
        color (formPair n (highClass n j) high).2) ↔
      (uniformLow a b low).1 = (uniformLow a b low).2 ∧
        (uniformHigh a b high).1 = (uniformHigh a b high).2 := by
  have hsub : ((j-1 : Nat) : ZMod n) = (j : ZMod n)-1 := by
    rw [Nat.cast_sub hj]; simp
  have hneg : -((j-1 : Nat) : ZMod n) = 1-(j : ZMod n) := by rw [hsub]; ring
  have hcp : color ((j : ZMod n)-1) = a := by rw [← hsub]; exact hold.1
  have hcn : color (1-(j : ZMod n)) = a := by rw [← hneg]; exact hold.2
  have hh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
    simp only [highClass, Nat.cast_sub hjn, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add]
  have hhsub : (highClass n j : ZMod n)-1 = -(j : ZMod n) := by rw [hh]; ring
  have hhneg : -(highClass n j : ZMod n) = (j : ZMod n)-1 := by rw [hh]; ring
  have hhone : 1-(highClass n j : ZMod n) = (j : ZMod n) := by rw [hh]; ring
  have hl : (color (formPair n j low).1, color (formPair n j low).2) =
      uniformLow a b low := by
    fin_cases low <;> simp [formPair, List.get, uniformLow, hp, hm, hcp, hcn, hnew.1, hnew.2]
  have hhigh : (color (formPair n (highClass n j) high).1,
      color (formPair n (highClass n j) high).2) = uniformHigh a b high := by
    fin_cases high <;> simp [formPair, List.get, uniformHigh, hp, hm,
      hhsub, hhneg, hhone, hh, hcp, hcn, hnew.1, hnew.2]
  rw [← hl, ← hhigh]

private def pairColored (n j : Nat) (color : ZMod n → Bool) (f g : Form) : Prop :=
  color (formPair n j f).1 = color (formPair n j f).2 ∧
    color (formPair n (highClass n j) g).1 = color (formPair n (highClass n j) g).2

private theorem block_constraints (n j : Nat) (hj : 3 ≤ j) (hjn : j+2 ≤ n+1)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (b b' : Bool)
    (hold : color ((j-1 : Nat) : ZMod n) = b ∧ color (-((j-1 : Nat) : ZMod n)) = b)
    (hzero : color (j : ZMod n) = b ∧ color (-(j : ZMod n)) = b)
    (hone : color ((j+1 : Nat) : ZMod n) = b ∧ color (-((j+1 : Nat) : ZMod n)) = b)
    (htwo : color ((j+2 : Nat) : ZMod n) = b' ∧ color (-((j+2 : Nat) : ZMod n)) = b') :
    pairColored n j color (if b then Form.V else Form.III) (if b then Form.II else Form.IV) ∧
      pairColored n (j+1) color (if b then Form.II else Form.IV) (if b then Form.V else Form.III) ∧
      pairColored n (j+2) color (if b then Form.I else Form.VI) (if b' then Form.I else Form.VI) := by
  have hprevone : color ((j+1-1 : Nat) : ZMod n) = b ∧
      color (-((j+1-1 : Nat) : ZMod n)) = b := by simpa using hzero
  have hprevtwo : color ((j+2-1 : Nat) : ZMod n) = b ∧
      color (-((j+2-1 : Nat) : ZMod n)) = b := by
    simpa only [show j+2-1=j+1 by omega] using hone
  cases b
  · refine ⟨?_, ?_, ?_⟩
    · exact (uniform_pair_colors n j (by omega) (by omega) color hp hm _ _ false false
        hold hzero).mpr (by decide)
    · exact (uniform_pair_colors n (j+1) (by omega) (by omega) color hp hm _ _ false false
        hprevone hone).mpr (by decide)
    · apply (uniform_pair_colors n (j+2) (by omega) (by omega) color hp hm _ _ false b'
        hprevtwo htwo).mpr
      cases b' <;> decide
  · refine ⟨?_, ?_, ?_⟩
    · exact (uniform_pair_colors n j (by omega) (by omega) color hp hm _ _ true true
        hold hzero).mpr (by decide)
    · exact (uniform_pair_colors n (j+1) (by omega) (by omega) color hp hm _ _ true true
        hprevone hone).mpr (by decide)
    · apply (uniform_pair_colors n (j+2) (by omega) (by omega) color hp hm _ _ true b'
        hprevtwo htwo).mpr
      cases b' <;> decide

private theorem even_block_color {m : Nat} (n j : Nat) (color : ZMod n → Bool)
    (b b' : Bool) (p : EvenTail .positive m (bitState b'))
    (hc : pairColored n j color (if b then Form.V else Form.III) (if b then Form.II else Form.IV) ∧
      pairColored n (j+1) color (if b then Form.II else Form.IV) (if b then Form.V else Form.III) ∧
      pairColored n (j+2) color (if b then Form.I else Form.VI) (if b' then Form.I else Form.VI))
    (ht : EvenColorTail n color p (j+3)) :
    EvenColorTail n color (prependEvenBlock b b' p) j := by
  cases b <;> cases b' <;>
    exact ⟨hc.1.1, hc.1.2, hc.2.1.1, hc.2.1.2, hc.2.2.1, hc.2.2.2, ht⟩

private theorem odd_block_color {m : Nat} (n j : Nat) (color : ZMod n → Bool)
    (b b' : Bool) (p : OddTail .positive m (bitState b'))
    (hc : pairColored n j color (if b then Form.V else Form.III) (if b then Form.II else Form.IV) ∧
      pairColored n (j+1) color (if b then Form.II else Form.IV) (if b then Form.V else Form.III) ∧
      pairColored n (j+2) color (if b then Form.I else Form.VI) (if b' then Form.I else Form.VI))
    (ht : OddColorTail n color p (j+3)) :
    OddColorTail n color (prependOddBlock b b' p) j := by
  cases b <;> cases b' <;>
    exact ⟨hc.1.1, hc.1.2, hc.2.1.1, hc.2.1.2, hc.2.2.1, hc.2.2.2, ht⟩

private theorem even_band_colored (l n j : Nat) (b : Bool) (w : Fin l → Bool)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (hj : 3 ≤ j) (hn : n = 2*(j+evenWordLength l))
    (hfit : ∀ k, j-1 ≤ k → k ≤ j+evenWordLength l →
      color (k : ZMod n) = wordBand l b w (k-(j-1)) ∧
        color (-(k : ZMod n)) = wordBand l b w (k-(j-1))) :
    EvenColorTail n color (evenWordTail l b w) j := by
  induction l generalizing j b with
  | zero =>
      have hold := hfit (j-1) (by omega) (by simp [evenWordLength])
      have hcap := hfit j (by omega) (by simp [evenWordLength])
      simp only [wordBand] at hold hcap
      have hsub : ((j-1 : Nat) : ZMod n) = (j : ZMod n)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ j)]; simp
      have hneg : -((j-1 : Nat) : ZMod n) = 1-(j : ZMod n) := by rw [hsub]; ring
      have hh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
        simp only [highClass, Nat.cast_sub (by simp [evenWordLength] at hn; omega : j ≤ n+1),
          Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]
      have hhsub : (highClass n j : ZMod n)-1 = -(j : ZMod n) := by rw [hh]; ring
      have hhneg : -(highClass n j : ZMod n) = (j : ZMod n)-1 := by rw [hh]; ring
      have hhone : 1-(highClass n j : ZMod n) = (j : ZMod n) := by rw [hh]; ring
      cases b
      · change color (-1) = color (j : ZMod n) ∧
          color ((highClass n j : ZMod n)-1) = color (-(highClass n j : ZMod n))
        rw [hm, hcap.1, hhsub, hcap.2, hhneg, ← hsub, hold.1]
        exact ⟨rfl, rfl⟩
      · change color (-(j : ZMod n)) = color 1 ∧
          color (highClass n j : ZMod n) = color (1-(highClass n j : ZMod n))
        rw [hcap.2, hp, hhone, hcap.1, hh, ← hneg, hold.2]
        exact ⟨rfl, rfl⟩
  | succ l ih =>
      have htail : EvenColorTail n color
          (evenWordTail l (w 0) (fun i => w i.succ)) (j+3) := by
        apply ih (j+3) (w 0) (fun i => w i.succ) (by omega)
          (by simp only [evenWordLength] at hn; omega)
        intro k hlo hhi
        have hc := hfit k (by omega) (by simp only [evenWordLength] at hn hhi ⊢; omega)
        have hs := band_shift l b w j k (by omega) (by omega)
        simpa only [hs, show j+3-1=j+2 by omega] using hc
      have hbase (k : Nat) (hlo : j-1 ≤ k) (hhi : k ≤ j+1) :
          color (k : ZMod n) = b ∧ color (-(k : ZMod n)) = b := by
        have hc := hfit k hlo (by simp only [evenWordLength]; omega)
        simpa only [band_head (l+1) b w (k-(j-1)) (by omega)] using hc
      have hnext : color ((j+2 : Nat) : ZMod n) = w 0 ∧
          color (-((j+2 : Nat) : ZMod n)) = w 0 := by
        have hc := hfit (j+2) (by omega) (by simp only [evenWordLength]; omega)
        have hs : wordBand (l+1) b w (j+2-(j-1)) = w 0 := by
          rw [band_shift l b w j (j+2) (by omega) (by omega)]
          simpa only [Nat.sub_self] using band_head l (w 0) (fun i => w i.succ) 0 (by omega)
        simpa only [hs] using hc
      exact even_block_color n j color b (w 0) _
        (block_constraints n j hj (by simp only [evenWordLength] at hn; omega)
          color hp hm b (w 0) (hbase (j-1) (by omega) (by omega))
          (hbase j (by omega) (by omega)) (hbase (j+1) (by omega) (by omega)) hnext) htail

private theorem odd_band_colored (l n j : Nat) (b : Bool) (w : Fin l → Bool)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (hj : 3 ≤ j) (hn : n+1 = 2*(j+oddWordLength l))
    (hfit : ∀ k, j-1 ≤ k → k ≤ j+oddWordLength l-1 →
      color (k : ZMod n) = wordBand l b w (k-(j-1)) ∧
        color (-(k : ZMod n)) = wordBand l b w (k-(j-1))) :
    OddColorTail n color (oddWordTail l b w) j := by
  induction l generalizing j b with
  | zero =>
      have hold := hfit (j-1) (by omega) (by simp [oddWordLength]; omega)
      have hzero := hfit j (by omega) (by simp [oddWordLength])
      have hone := hfit (j+1) (by omega) (by simp [oddWordLength])
      simp only [wordBand] at hold hzero hone
      have hprev : color ((j+1-1 : Nat) : ZMod n) = b ∧
          color (-((j+1-1 : Nat) : ZMod n)) = b := by simpa using hzero
      have hbound : j+1 ≤ n+1 := by simp only [oddWordLength] at hn; omega
      cases b
      · have h0 := (uniform_pair_colors n j (by omega) (by omega) color hp hm
          Form.III Form.IV false false hold hzero).mpr (by decide)
        have h1 := (uniform_pair_colors n (j+1) (by omega) hbound color hp hm
          Form.IV Form.III false false hprev hone).mpr (by decide)
        refine ⟨h0.1, h0.2, h1.1, h1.2, ?_⟩
        change color (1-((j+2 : Nat) : ZMod n)) = color (-1)
        have he : 1-((j+2 : Nat) : ZMod n) = -((j+1 : Nat) : ZMod n) := by
          push_cast; ring
        rw [he, hone.2, hm]
      · have h0 := (uniform_pair_colors n j (by omega) (by omega) color hp hm
          Form.V Form.II true true hold hzero).mpr (by decide)
        have h1 := (uniform_pair_colors n (j+1) (by omega) hbound color hp hm
          Form.II Form.V true true hprev hone).mpr (by decide)
        refine ⟨h0.1, h0.2, h1.1, h1.2, ?_⟩
        change color 1 = color (((j+2 : Nat) : ZMod n)-1)
        have he : (((j+2 : Nat) : ZMod n)-1) = ((j+1 : Nat) : ZMod n) := by
          push_cast; ring
        rw [he, hone.1, hp]
  | succ l ih =>
      have htail : OddColorTail n color
          (oddWordTail l (w 0) (fun i => w i.succ)) (j+3) := by
        apply ih (j+3) (w 0) (fun i => w i.succ) (by omega)
          (by simp only [oddWordLength] at hn; omega)
        intro k hlo hhi
        have hc := hfit k (by omega) (by simp only [oddWordLength] at hn hhi ⊢; omega)
        have hs := band_shift l b w j k (by omega) (by omega)
        simpa only [hs, show j+3-1=j+2 by omega] using hc
      have hbase (k : Nat) (hlo : j-1 ≤ k) (hhi : k ≤ j+1) :
          color (k : ZMod n) = b ∧ color (-(k : ZMod n)) = b := by
        have hc := hfit k hlo (by simp only [oddWordLength]; omega)
        simpa only [band_head (l+1) b w (k-(j-1)) (by omega)] using hc
      have hnext : color ((j+2 : Nat) : ZMod n) = w 0 ∧
          color (-((j+2 : Nat) : ZMod n)) = w 0 := by
        have hc := hfit (j+2) (by omega) (by simp only [oddWordLength]; omega)
        have hs : wordBand (l+1) b w (j+2-(j-1)) = w 0 := by
          rw [band_shift l b w j (j+2) (by omega) (by omega)]
          simpa only [Nat.sub_self] using band_head l (w 0) (fun i => w i.succ) 0 (by omega)
        simpa only [hs] using hc
      exact odd_block_color n j color b (w 0) _
        (block_constraints n j hj (by simp only [oddWordLength] at hn; omega)
          color hp hm b (w 0) (hbase (j-1) (by omega) (by omega))
          (hbase j (by omega) (by omega)) (hbase (j+1) (by omega) (by omega)) hnext) htail

private theorem even_code_forms (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    evenPathForms (evenCodedPath r hr b w).1 = evenPathForms (evenWordPath (r-1) b w) := by
  have transport {m k : Nat} (h : m = k)
      (p : {p : EvenPath .positive m // evenPathCharge p = 0}) :
      evenPathForms (h ▸ p).1 = evenPathForms p.1 := by cases h; rfl
  exact transport (by rw [even_word_length]; omega) _

private theorem odd_code_forms (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    oddPathForms (oddCodedPath r hr b w).1 = oddPathForms (oddWordPath (r-1) b w) := by
  have transport {m k : Nat} (h : m = k)
      (p : {p : OddPath .positive m // oddPathCharge p = 0}) :
      oddPathForms (h ▸ p).1 = oddPathForms p.1 := by cases h; rfl
  exact transport (by rw [odd_word_length]; omega) _

/-- Every absolute word has an actual coloring of all native chosen class edges.
Activity of both roots is a separate condition, not asserted by this theorem. -/
theorem even_native_code_coloring (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    ∃ color : ZMod (3*(2*r)) → Bool, color 1 = true ∧ color (-1) = false ∧
      ∀ i, color (chosenPair (evenCodedChoice r hr b w).1 i).1 =
        color (chosenPair (evenCodedChoice r hr b w).1 i).2 := by
  let color : ZMod (3*(2*r)) → Bool :=
    radialColor (3*(2*r)) (fun k => wordBand (r-1) b w (k-2))
  have hroot := radial_roots (3*(2*r)) (by omega) (fun k => wordBand (r-1) b w (k-2))
  have hp : color 1 = true := hroot.1
  have hm : color (-1) = false := hroot.2
  have htail : EvenColorTail (3*(2*r)) color (evenWordTail (r-1) b w) 3 := by
    apply even_band_colored (r-1) (3*(2*r)) 3 b w color hp hm (by omega)
      (by rw [even_word_length]; omega)
    intro k hlo hhi
    exact radial_interior (3*(2*r)) k (by omega)
      (by rw [even_word_length] at hhi; omega) _
  have htwo : color (2 : ZMod (3*(2*r))) = b ∧
      color (-(2 : ZMod (3*(2*r)))) = b := by
    have h := radial_interior (3*(2*r)) 2 (by omega) (by omega)
      (fun k => wordBand (r-1) b w (k-2))
    simpa only [color, Nat.cast_ofNat, Nat.sub_self, band_head (r-1) b w 0 (by omega)] using h
  have hedge : ∀ e ∈ formsEdges (3*(2*r)) 2 (evenPathForms (evenWordPath (r-1) b w)),
      color e.1 = color e.2 := by
    intro e he
    cases b
    · simp only [evenWordPath, evenPathForms, formsEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simpa [formPair, startValue, starts, List.get, Form.II, Form.IV, show (1 : ZMod _) - 2 = -1 by ring] using htwo.1.trans hm.symm
      · exact (even_color_edges _ color _ 3 (by rw [even_word_length]; omega)).mp htail e he
    · simp only [evenWordPath, evenPathForms, formsEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simpa [formPair, startValue, starts, List.get, Form.II, Form.IV, show (2 : ZMod _) - 1 = 1 by ring] using hp.trans htwo.2.symm
      · exact (even_color_edges _ color _ 3 (by rw [even_word_length]; omega)).mp htail e he
  refine ⟨color, hp, hm, ?_⟩
  intro i
  have he := (choice_edges_mem (evenCodedChoice r hr b w).1 _).mpr ⟨i, rfl⟩
  change chosenPair (evenCodedChoice r hr b w).1 i ∈
    formsEdges (3*(2*r)) 2 (choiceForms (evenPathChoices r hr (evenCodedPath r hr b w).1)) at he
  rw [even_decode_forms, even_code_forms] at he
  exact hedge _ he

/-- The odd native realization includes the two final transitions and singleton cap. -/
theorem odd_native_code_coloring (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    ∃ color : ZMod (3*(2*r+1)) → Bool, color 1 = true ∧ color (-1) = false ∧
      ∀ i, color (chosenPair (oddCodedChoice r hr b w).1 i).1 =
        color (chosenPair (oddCodedChoice r hr b w).1 i).2 := by
  let color : ZMod (3*(2*r+1)) → Bool :=
    radialColor (3*(2*r+1)) (fun k => wordBand (r-1) b w (k-2))
  have hroot := radial_roots (3*(2*r+1)) (by omega) (fun k => wordBand (r-1) b w (k-2))
  have hp : color 1 = true := hroot.1
  have hm : color (-1) = false := hroot.2
  have htail : OddColorTail (3*(2*r+1)) color (oddWordTail (r-1) b w) 3 := by
    apply odd_band_colored (r-1) (3*(2*r+1)) 3 b w color hp hm (by omega)
      (by rw [odd_word_length]; omega)
    intro k hlo hhi
    exact radial_interior (3*(2*r+1)) k (by omega)
      (by rw [odd_word_length] at hhi; omega) _
  have htwo : color (2 : ZMod (3*(2*r+1))) = b ∧
      color (-(2 : ZMod (3*(2*r+1)))) = b := by
    have h := radial_interior (3*(2*r+1)) 2 (by omega) (by omega)
      (fun k => wordBand (r-1) b w (k-2))
    simpa only [color, Nat.cast_ofNat, Nat.sub_self, band_head (r-1) b w 0 (by omega)] using h
  have hedge : ∀ e ∈ formsEdges (3*(2*r+1)) 2 (oddPathForms (oddWordPath (r-1) b w)),
      color e.1 = color e.2 := by
    intro e he
    cases b
    · simp only [oddWordPath, oddPathForms, formsEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simpa [formPair, startValue, starts, List.get, Form.II, Form.IV, show (1 : ZMod _) - 2 = -1 by ring] using htwo.1.trans hm.symm
      · exact (odd_color_edges _ color _ 3 (by rw [odd_word_length]; omega)).mp htail e he
    · simp only [oddWordPath, oddPathForms, formsEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simpa [formPair, startValue, starts, List.get, Form.II, Form.IV, show (2 : ZMod _) - 1 = 1 by ring] using hp.trans htwo.2.symm
      · exact (odd_color_edges _ color _ 3 (by rw [odd_word_length]; omega)).mp htail e he
  refine ⟨color, hp, hm, ?_⟩
  intro i
  have he := (choice_edges_mem (oddCodedChoice r hr b w).1 _).mpr ⟨i, rfl⟩
  change chosenPair (oddCodedChoice r hr b w).1 i ∈
    formsEdges (3*(2*r+1)) 2 (choiceForms (oddPathChoices r hr (oddCodedPath r hr b w).1)) at he
  rw [odd_decode_forms, odd_code_forms] at he
  exact hedge _ he

private def rootVertex (n : Nat) (s : Bool) : ZMod n := if s then 1 else -1

private def rootForm (s : Bool) (f : Form) : Prop :=
  if s then f = Form.I ∨ f = Form.V else f = Form.III ∨ f = Form.VI

private def rootAt (n : Nat) (s : Bool) (e : ZMod n × ZMod n) : Prop :=
  e.1 = rootVertex n s ∨ e.2 = rootVertex n s

private theorem interior_not_roots (n k : Nat) (hk : 2 ≤ k) (hkn : 2*k ≤ n) :
    (k : ZMod n) ≠ 1 ∧ (k : ZMod n) ≠ -1 ∧
      -(k : ZMod n) ≠ 1 ∧ -(k : ZMod n) ≠ -1 := by
  have hr := radius_nat n k (by omega) hkn
  have hone := radius_nat n 1 (by omega) (by omega)
  simp only [Nat.cast_one] at hone
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro h; have he := congrArg (supportRadius n) h
  · rw [hr.1, hone.1] at he; omega
  · rw [hr.1, hone.2] at he; omega
  · rw [hr.2, hone.1] at he; omega
  · rw [hr.2, hone.2] at he; omega

private theorem pair_root_incidence (n j : Nat) (hj : 3 ≤ j) (hjn : 2*j ≤ n)
    (s : Bool) (f : Form) :
    (rootAt n s (formPair n j f) ↔ rootForm s f) ∧
      (rootAt n s (formPair n (highClass n j) f) ↔ rootForm s f) := by
  have hp := interior_not_roots n j (by omega) hjn
  have hm := interior_not_roots n (j-1) (by omega) (by omega)
  have hroot : (-1 : ZMod n) ≠ 1 := by
    intro h
    have he := ZMod.neg_one_eq_one_iff.mp h
    omega
  have hsub : (j : ZMod n)-1 = ((j-1 : Nat) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; simp
  have hneg : 1-(j : ZMod n) = -((j-1 : Nat) : ZMod n) := by rw [← hsub]; ring
  have hh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
    simp only [highClass, Nat.cast_sub (by omega : j ≤ n+1),
      Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]
  have hhsub : (highClass n j : ZMod n)-1 = -(j : ZMod n) := by rw [hh]; ring
  have hhneg : -(highClass n j : ZMod n) = ((j-1 : Nat) : ZMod n) := by
    rw [hh, ← hsub]; ring
  have hhone : 1-(highClass n j : ZMod n) = (j : ZMod n) := by rw [hh]; ring
  have low_table : formPair n j f =
      [(1,((j-1 : Nat) : ZMod n)), ((j : ZMod n),-((j-1 : Nat) : ZMod n)),
        (-1,(j : ZMod n)), (((j-1 : Nat) : ZMod n),-(j : ZMod n)),
        (-(j : ZMod n),1), (-((j-1 : Nat) : ZMod n),-1)].get f := by
    fin_cases f <;> simp [formPair, List.get, hsub, hneg]
  have high_table : formPair n (highClass n j) f =
      [(1,-(j : ZMod n)), (-((j-1 : Nat) : ZMod n),(j : ZMod n)),
        (-1,-((j-1 : Nat) : ZMod n)), (-(j : ZMod n),((j-1 : Nat) : ZMod n)),
        (((j-1 : Nat) : ZMod n),1), ((j : ZMod n),-1)].get f := by
    fin_cases f <;> simp [formPair, List.get, hhsub, hhneg, hhone, hh, hsub, hneg] <;> rw [← hsub] <;> ring
  rw [low_table, high_table]
  cases s <;> fin_cases f <;>
    simp [rootAt, rootVertex, rootForm, List.get,
      Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI,
      hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2,
      hroot, Ne.symm hroot]

private def rootTouches (n : Nat) (s : Bool) (es : List (ZMod n × ZMod n)) : Prop :=
  ∃ e ∈ es, rootAt n s e

private theorem touches_cons (n : Nat) (s : Bool) (e : ZMod n × ZMod n)
    (es : List (ZMod n × ZMod n)) :
    rootTouches n s (e::es) ↔ rootAt n s e ∨ rootTouches n s es := by
  simp [rootTouches, or_and_right, exists_or]

private theorem touches_append (n : Nat) (s : Bool)
    (es fs : List (ZMod n × ZMod n)) :
    rootTouches n s (es++fs) ↔ rootTouches n s es ∨ rootTouches n s fs := by
  simp [rootTouches, or_and_right, exists_or]

private theorem even_step_touches {m : Nat} {state : State} (n j : Nat)
    (hj : 3 ≤ j) (hn : n = 2*(j+(m+1))) (s : Bool)
    (i : StepIndex state) (p : EvenTail .positive m (stepTarget i)) :
    rootTouches n s (formsEdges n j
      (evenTailLowForms (h := .positive) (m := m+1) (⟨i,p⟩ : EvenTail .positive (m+1) state) ++
        (evenTailHighForms (h := .positive) (m := m+1) (⟨i,p⟩ : EvenTail .positive (m+1) state)).reverse)) ↔
      rootForm s (stepValue (h := .positive) i).low ∨
        rootForm s (stepValue (h := .positive) i).high ∨
          rootTouches n s (formsEdges n (j+1) (evenTailLowForms p ++ (evenTailHighForms p).reverse)) := by
  rw [even_edges_peel i p (by omega), touches_cons, touches_append, touches_cons]
  have hl := (pair_root_incidence n j hj (by omega) s (stepValue (h := .positive) i).low).1
  have hh := (pair_root_incidence n j hj (by omega) s (stepValue (h := .positive) i).high).2
  simp only [hl, hh, rootTouches, List.not_mem_nil, false_and, exists_false, or_false]
  exact or_congr Iff.rfl or_comm

private theorem odd_step_touches {m : Nat} {state : State} (n j : Nat)
    (hj : 3 ≤ j) (hn : n+1 = 2*(j+(m+1))) (s : Bool)
    (i : StepIndex state) (p : OddTail .positive m (stepTarget i)) :
    rootTouches n s (formsEdges n j
      (oddTailLowForms (h := .positive) (m := m+1) (⟨i,p⟩ : OddTail .positive (m+1) state) ++
        (oddTailHighForms (h := .positive) (m := m+1) (⟨i,p⟩ : OddTail .positive (m+1) state)).reverse)) ↔
      rootForm s (stepValue (h := .positive) i).low ∨
        rootForm s (stepValue (h := .positive) i).high ∨
          rootTouches n s (formsEdges n (j+1) (oddTailLowForms p ++ (oddTailHighForms p).reverse)) := by
  rw [odd_edges_peel i p (by omega), touches_cons, touches_append, touches_cons]
  have hl := (pair_root_incidence n j hj (by omega) s (stepValue (h := .positive) i).low).1
  have hh := (pair_root_incidence n j hj (by omega) s (stepValue (h := .positive) i).high).2
  simp only [hl, hh, rootTouches, List.not_mem_nil, false_and, exists_false, or_false]
  exact or_congr Iff.rfl or_comm

private theorem word_root_succ (l : Nat) (w : Fin (l+1) → Bool) (s : Bool) :
    (∃ i, w i = s) ↔ w 0 = s ∨ ∃ i : Fin l, w i.succ = s := by
  constructor
  · rintro ⟨i, hi⟩
    exact Fin.cases (fun h => Or.inl h) (fun i h => Or.inr ⟨i,h⟩) i hi
  · rintro (h | ⟨i,hi⟩)
    · exact ⟨0,h⟩
    · exact ⟨i.succ,hi⟩

private theorem even_block_touches {m : Nat} (n j : Nat) (b b' s : Bool)
    (p : EvenTail .positive m (bitState b')) (hj : 3 ≤ j)
    (hn : n = 2*(j+(m+3))) :
    rootTouches n s (formsEdges n j
      (evenTailLowForms (prependEvenBlock b b' p) ++
        (evenTailHighForms (prependEvenBlock b b' p)).reverse)) ↔
      b = s ∨ b' = s ∨ rootTouches n s
        (formsEdges n (j+3) (evenTailLowForms p ++ (evenTailHighForms p).reverse)) := by
  cases b <;> cases b' <;> cases s
  all_goals
    dsimp only [prependEvenBlock, bitState]
    erw [even_step_touches n j hj (by omega),
      even_step_touches n (j+1) (by omega) (by omega),
      even_step_touches n (j+1+1) (by omega) (by omega)]
    simp [rootForm, stepValue, positiveStepLabel, stepTarget, stepTargets,
      State.A, State.D, State.E, show j+1+1+1=j+3 by omega] <;> tauto

private theorem odd_block_touches {m : Nat} (n j : Nat) (b b' s : Bool)
    (p : OddTail .positive m (bitState b')) (hj : 3 ≤ j)
    (hn : n+1 = 2*(j+(m+3))) :
    rootTouches n s (formsEdges n j
      (oddTailLowForms (prependOddBlock b b' p) ++
        (oddTailHighForms (prependOddBlock b b' p)).reverse)) ↔
      b = s ∨ b' = s ∨ rootTouches n s
        (formsEdges n (j+3) (oddTailLowForms p ++ (oddTailHighForms p).reverse)) := by
  cases b <;> cases b' <;> cases s
  all_goals
    dsimp only [prependOddBlock, bitState]
    erw [odd_step_touches n j hj (by omega),
      odd_step_touches n (j+1) (by omega) (by omega),
      odd_step_touches n (j+1+1) (by omega) (by omega)]
    simp [rootForm, stepValue, positiveStepLabel, stepTarget, stepTargets,
      State.A, State.D, State.E, show j+1+1+1=j+3 by omega] <;> tauto

private theorem even_word_touches (l n j : Nat) (b : Bool) (w : Fin l → Bool)
    (s : Bool) (hj : 3 ≤ j) (hn : n = 2*(j+evenWordLength l)) :
    rootTouches n s (formsEdges n j (evenTailLowForms (evenWordTail l b w) ++
      (evenTailHighForms (evenWordTail l b w)).reverse)) ↔ b = s ∨ ∃ i, w i = s := by
  induction l generalizing j b with
  | zero =>
      have hk : highClass n j = j+1 := by simp only [highClass, evenWordLength] at *; omega
      have hl (f : Form) := (pair_root_incidence n j hj
        (by simp only [evenWordLength] at hn; omega) s f).1
      have hh (f : Form) : rootAt n s (formPair n (j+1) f) ↔ rootForm s f := by
        rw [← hk]
        exact (pair_root_incidence n j hj (by simp only [evenWordLength] at hn; omega) s f).2
      cases b
      · change rootTouches n s (formsEdges n j [Form.III, Form.IV]) ↔ false = s ∨ ∃ i, w i = s
        simp only [formsEdges, touches_cons]
        cases s <;> simp [hl, hh, rootTouches, rootForm, Form.I, Form.III, Form.IV, Form.V, Form.VI]
      · change rootTouches n s (formsEdges n j [Form.V, Form.II]) ↔ true = s ∨ ∃ i, w i = s
        simp only [formsEdges, touches_cons]
        cases s <;> simp [hl, hh, rootTouches, rootForm, Form.I, Form.II, Form.III, Form.V, Form.VI]
  | succ l ih =>
      have ht := ih (j+3) (w 0) (fun i => w i.succ) (by omega)
        (by simp only [evenWordLength] at hn; omega)
      refine (even_block_touches n j b (w 0) s
        (evenWordTail l (w 0) (fun i => w i.succ)) hj
        (by simpa only [evenWordLength] using hn)).trans ?_
      rw [ht, word_root_succ]
      tauto

private theorem odd_word_touches (l n j : Nat) (b : Bool) (w : Fin l → Bool)
    (s : Bool) (hj : 3 ≤ j) (hn : n+1 = 2*(j+oddWordLength l)) :
    rootTouches n s (formsEdges n j (oddTailLowForms (oddWordTail l b w) ++
      (oddTailHighForms (oddWordTail l b w)).reverse)) ↔ b = s ∨ ∃ i, w i = s := by
  induction l generalizing j b with
  | zero =>
      have hnr := interior_not_roots n (j+1) (by omega)
        (by simp only [oddWordLength] at hn; omega)
      have hs : (((j+1+1 : Nat) : ZMod n)-1) = ((j+1 : Nat) : ZMod n) := by
        push_cast; ring
      have hm : 1-((j+1+1 : Nat) : ZMod n) = -((j+1 : Nat) : ZMod n) := by
        push_cast; ring
      have hnrp : (j : ZMod n) + 1 ≠ -1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hnr.2.1
      have hnrm : -1 + -(j : ZMod n) ≠ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev] using hnr.2.2.1
      have hroot : (-1 : ZMod n) ≠ 1 := by
        intro h
        have he := ZMod.neg_one_eq_one_iff.mp h
        simp only [oddWordLength] at hn
        omega
      cases b <;> cases s
      all_goals
        simp only [oddWordTail, oddFinal]
        dsimp only [bitState]
        erw [odd_step_touches n j hj (by simp only [oddWordLength] at hn; omega),
          odd_step_touches n (j+1) (by omega) (by simp only [oddWordLength] at hn; omega)]
        simp [bitState, rootForm, stepValue, positiveStepLabel, stepTarget, stepTargets,
          State.A, State.D, State.E, Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI,
          rootTouches, oddTailLowForms, oddTailHighForms,
          oddTerminalValue, formsEdges, rootAt, rootVertex, formPair, List.get,
          hs, hm, hnr.1, hnr.2.1, hnr.2.2.1, hnr.2.2.2, hnrp, hnrm,
          hroot, Ne.symm hroot]
  | succ l ih =>
      have ht := ih (j+3) (w 0) (fun i => w i.succ) (by omega)
        (by simp only [oddWordLength] at hn; omega)
      refine (odd_block_touches n j b (w 0) s
        (oddWordTail l (w 0) (fun i => w i.succ)) hj
        (by simpa only [oddWordLength] using hn)).trans ?_
      rw [ht, word_root_succ]
      tauto

private theorem start_root_incidence (n : Nat) (hn : 6 ≤ n) (b s : Bool) :
    rootAt n s (formPair n 2 (startValue (h := .positive) (if b then 1 else 0)).label) ↔
      b = s := by
  have hi := interior_not_roots n 2 (by omega) (by omega)
  simp only [Nat.cast_ofNat] at hi
  have hr : (-1 : ZMod n) ≠ 1 := by
    intro h
    have he := ZMod.neg_one_eq_one_iff.mp h
    omega
  have ht : (2 : ZMod n)-1 = 1 := by ring
  have hm : 1-(2 : ZMod n) = -1 := by ring
  cases b <;> cases s <;>
    simp [rootAt, rootVertex, startValue, starts, formPair, List.get,
      Form.II, Form.IV, ht, hm, Nat.cast_ofNat,
      hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, hr, Ne.symm hr]

private theorem active_root_touches {t : Nat} (c : Choices t) (s : Bool) :
    Active c (rootVertex (3*t) s) ↔
      rootTouches (3*t) s (formsEdges (3*t) 2 (choiceForms c)) := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨chosenPair c i, (choice_edges_mem c _).mpr ⟨i,rfl⟩, hi⟩
  · rintro ⟨e,he,hr⟩
    obtain ⟨i,rfl⟩ := (choice_edges_mem c e).mp he
    exact ⟨i,hr⟩

/-- Activity refers to the actual selected endpoints; unused roots are excluded. -/
theorem even_code_root_activity (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) (s : Bool) :
    Active (evenCodedChoice r hr b w).1 (if s then 1 else -1) ↔
      b = s ∨ ∃ i, w i = s := by
  rw [show (if s then 1 else -1) = rootVertex (3*(2*r)) s by rfl, active_root_touches]
  change rootTouches (3*(2*r)) s (formsEdges (3*(2*r)) 2
    (choiceForms (evenPathChoices r hr (evenCodedPath r hr b w).1))) ↔ _
  rw [even_decode_forms, even_code_forms]
  have ht := even_word_touches (r-1) (3*(2*r)) 3 b w s (by omega)
    (by rw [even_word_length]; omega)
  have hs := start_root_incidence (3*(2*r)) (by omega) b s
  cases b
  · change rootTouches _ s (formPair _ 2 (startValue (h := .positive) 0).label ::
      formsEdges _ 3 (evenTailLowForms (evenWordTail (r-1) false w) ++
        (evenTailHighForms (evenWordTail (r-1) false w)).reverse)) ↔ _
    erw [touches_cons, hs, ht]
    exact ⟨fun h => h.elim Or.inl id, Or.inr⟩
  · change rootTouches _ s (formPair _ 2 (startValue (h := .positive) 1).label ::
      formsEdges _ 3 (evenTailLowForms (evenWordTail (r-1) true w) ++
        (evenTailHighForms (evenWordTail (r-1) true w)).reverse)) ↔ _
    erw [touches_cons, hs, ht]
    exact ⟨fun h => h.elim Or.inl id, Or.inr⟩

/-- The singleton-cap code has the same exact activity condition on native choices. -/
theorem odd_code_root_activity (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) (s : Bool) :
    Active (oddCodedChoice r hr b w).1 (if s then 1 else -1) ↔
      b = s ∨ ∃ i, w i = s := by
  rw [show (if s then 1 else -1) = rootVertex (3*(2*r+1)) s by rfl, active_root_touches]
  change rootTouches (3*(2*r+1)) s (formsEdges (3*(2*r+1)) 2
    (choiceForms (oddPathChoices r hr (oddCodedPath r hr b w).1))) ↔ _
  rw [odd_decode_forms, odd_code_forms]
  have ht := odd_word_touches (r-1) (3*(2*r+1)) 3 b w s (by omega)
    (by rw [odd_word_length]; omega)
  have hs := start_root_incidence (3*(2*r+1)) (by omega) b s
  cases b
  · change rootTouches _ s (formPair _ 2 (startValue (h := .positive) 0).label ::
      formsEdges _ 3 (oddTailLowForms (oddWordTail (r-1) false w) ++
        (oddTailHighForms (oddWordTail (r-1) false w)).reverse)) ↔ _
    erw [touches_cons, hs, ht]
    exact ⟨fun h => h.elim Or.inl id, Or.inr⟩
  · change rootTouches _ s (formPair _ 2 (startValue (h := .positive) 1).label ::
      formsEdges _ 3 (oddTailLowForms (oddWordTail (r-1) true w) ++
        (oddTailHighForms (oddWordTail (r-1) true w)).reverse)) ↔ _
    erw [touches_cons, hs, ht]
    exact ⟨fun h => h.elim Or.inl id, Or.inr⟩

private theorem both_bits_iff (l : Nat) (b : Bool) (w : Fin l → Bool) :
    ((b = true ∨ ∃ i, w i = true) ∧ (b = false ∨ ∃ i, w i = false)) ↔
      w ≠ (fun _ => b) := by
  classical
  constructor
  · rintro ⟨hp,hm⟩ he
    subst w
    cases b <;> simp_all
  · intro h
    have hex : ∃ i, w i ≠ b := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨i,hi⟩ := hex
    cases b
    · refine ⟨Or.inr ⟨i,?_⟩, Or.inl rfl⟩
      cases he : w i <;> simp_all
    · refine ⟨Or.inl rfl, Or.inr ⟨i,?_⟩⟩
      cases he : w i <;> simp_all

/-- Absolute successor states exclude precisely the constant initial-state word. -/
theorem even_code_disconnected (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    ¬ ActiveConnected (evenCodedChoice r hr b w).1 ↔ w ≠ (fun _ => b) := by
  rw [actual_disconnected_iff_coloring (2*r) (by omega) _ (evenCodedChoice r hr b w).2]
  have hp := even_code_root_activity r hr b w true
  have hm := even_code_root_activity r hr b w false
  simp only [Bool.false_eq_true, ite_false, ite_true] at hp hm
  rw [hp, hm]
  have hc := even_native_code_coloring r hr b w
  exact ⟨fun h => (both_bits_iff (r-1) b w).mp ⟨h.1,h.2.1⟩,
    fun h => ⟨((both_bits_iff (r-1) b w).mpr h).1,
      ((both_bits_iff (r-1) b w).mpr h).2,hc⟩⟩

/-- The odd cap obeys the same activity exclusion, with every native label retained. -/
theorem odd_code_disconnected (r : Nat) (hr : 1 ≤ r) (b : Bool)
    (w : Fin (r-1) → Bool) :
    ¬ ActiveConnected (oddCodedChoice r hr b w).1 ↔ w ≠ (fun _ => b) := by
  rw [actual_disconnected_iff_coloring (2*r+1) (by omega) _ (oddCodedChoice r hr b w).2]
  have hp := odd_code_root_activity r hr b w true
  have hm := odd_code_root_activity r hr b w false
  simp only [Bool.false_eq_true, ite_false, ite_true] at hp hm
  rw [hp, hm]
  have hc := odd_native_code_coloring r hr b w
  exact ⟨fun h => (both_bits_iff (r-1) b w).mp ⟨h.1,h.2.1⟩,
    fun h => ⟨((both_bits_iff (r-1) b w).mpr h).1,
      ((both_bits_iff (r-1) b w).mpr h).2,hc⟩⟩

end D5.S3.Combinatorics.Zigzag
