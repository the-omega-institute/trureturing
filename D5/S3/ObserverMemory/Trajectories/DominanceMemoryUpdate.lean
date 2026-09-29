/- GID: D5/S3/ObserverMemory/Trajectories/DominanceMemoryUpdate
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/DominanceMemoryUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.MinMax]
   utility: none
   digest: Exact dominance memory updates and original readout for every binary window. -/

import D5.S3.TotalVariation.ParrySharedZeroRule
import Mathlib.Data.Finset.Lattice.Fold

namespace D5.S3.ObserverMemory.Trajectories.DominanceMemoryUpdate

open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
open D5.S3.TotalVariation.ParrySharedZeroRule

set_option autoImplicit false

/-- Coordinates `i` in this file correspond to source coordinates `i-R`.
The anchor after a closing endpoint `b` has coordinate `b+1-R`. -/
def runLength (c : ℕ × ℕ) : ℕ := c.2 - c.1 - 1

/-- All and only complete positive runs not dominated by a later closing run. -/
noncomputable def undominated (R : ℕ) (s : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (candidates s R R).filter fun c =>
    ∀ d ∈ candidates s R R, c.2 < d.2 → runLength d < runLength c

/-- Parity of every actual zero strictly after the closing endpoint. -/
def phase (R : ℕ) (s : Finset ℕ) (b : ℕ) : Bool := decide (transport s b R = 1)

/-- One past the latest observed one, or zero if none was observed. -/
def pastLast (s : Finset ℕ) : ℕ := s.sup (fun i => i+1)

/-- The entire stored state: endpoint/phase records and a truncated zero suffix. -/
abbrev Memory := Finset ((ℕ × ℕ) × Bool) × ℕ

noncomputable def encode (R : ℕ) (s : Finset ℕ) : Memory := by
  classical
  exact ((undominated R s).image (fun c => (c, phase R s c.2)), R - pastLast s)

noncomputable def memory {R : ℕ} (w : Fin R → Bool) : Memory := encode R (windowOnes w)

/-- Shift the actual window, then read the new bit at its newest position. -/
def shiftWindow {R : ℕ} (w : Fin R → Bool) (x : Bool) : Fin R → Bool :=
  fun i => if h : i.val + 1 < R then w ⟨i.val+1,h⟩ else x

/-- Only actual surviving records are transported. No window is stored or reread. -/
noncomputable def update (R : ℕ) (m : Memory) (x : Bool) : Memory := by
  classical
  let survivors := (m.1.filter (fun r => 0 < r.1.1)).image
    (fun r => ((r.1.1-1,r.1.2-1), xor r.2 (!x)))
  let records := if x = true ∧ 1 ≤ m.2 ∧ m.2 + 2 ≤ R then
    insert ((R-m.2-2,R-1),false)
      (survivors.filter fun r => m.2 < runLength r.1)
    else survivors
  exact (records, if x then 0 else min R (m.2+1))

/-- A single readout returns the selected endpoints, the following vertex as
anchor, and the transported direction. -/
noncomputable def readout (R : ℕ) (m : Memory) : Option (ℕ × ℕ) × Option ℕ × Bool :=
  match m.1.toList.argmax (fun r => score R r.1) with
  | none => (none,none,false)
  | some r => (some r.1,some (r.1.2+1),r.2)

/-- The actual observed one positions after dropping the oldest bit and appending x. -/
def shiftOnes (R : ℕ) (s : Finset ℕ) (x : Bool) : Finset ℕ :=
  ((s.filter fun i => 0 < i).image fun i => i-1) ∪
    (if x then {R-1} else ∅)

/-- Complete positive runs in an arbitrary actual window survive exactly when
their left endpoint survives. A new run is precisely a closed nonempty zero
suffix with a surviving observed left one. Actual transport counts all zeros. -/
theorem actual_complete_runs_shift (R : ℕ) (hR : 1 ≤ R) (s : Finset ℕ)
    (hs : ∀ i ∈ s, i < R) (x : Bool) :
    let t := shiftOnes R s x
    let ell := R - pastLast s
    (∀ c : ℕ × ℕ, c ∈ candidates t R R ↔
      (c.2 < R-1 ∧ (c.1+1,c.2+1) ∈ candidates s R R) ∨
      ((x = true ∧ 1 ≤ ell ∧ ell+2 ≤ R) ∧ c = (R-ell-2,R-1))) ∧
    (R - pastLast t = if x then 0 else min R (ell+1)) ∧
    (∀ b : ℕ, 0 < b → b < R → phase R t (b-1) = xor (phase R s b) (!x)) := by
  classical
  have cmem (s : Finset ℕ) (c : ℕ × ℕ) :
      c ∈ candidates s R R ↔ c.2 < R ∧ Complete s c.1 c.2 := by
    simp only [candidates, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨_,hb⟩,_,hc⟩
      exact ⟨hb,hc⟩
    · rintro ⟨hb,hc⟩
      exact ⟨⟨by have := hc.1; omega,hb⟩,by omega,hc⟩
  have lastProps (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) :
      pastLast s ≤ R ∧ (∀ i ∈ s, i < pastLast s) ∧
      (0 < pastLast s → pastLast s - 1 ∈ s) := by
    refine ⟨Finset.sup_le (fun i hi => by have := hs i hi; omega), ?_, ?_⟩
    · intro i hi
      have := Finset.le_sup (f := fun i : ℕ => i+1) hi
      change i < s.sup (fun i => i+1)
      omega
    · intro hp
      obtain ⟨i, hi, he⟩ := (Finset.le_sup_iff hp).mp (le_refl (pastLast s))
      have hl := Finset.le_sup (f := fun i : ℕ => i+1) hi
      have : pastLast s - 1 = i := by change i+1 ≤ pastLast s at hl; omega
      simpa [this] using hi
  let shifted := fun s : Finset ℕ => shiftOnes R s x
  have shiftMem (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) (i : ℕ) :
      i ∈ shifted s ↔ (i+1 < R ∧ i+1 ∈ s) ∨ (i = R-1 ∧ x = true) := by
    dsimp [shifted,shiftOnes]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    have hold : (∃ a, (a ∈ s ∧ 0 < a) ∧ a-1 = i) ↔ i+1 < R ∧ i+1 ∈ s := by
      constructor
      · rintro ⟨a, ⟨ha,hp⟩, he⟩
        have := hs a ha
        have : a = i+1 := by omega
        subst a
        exact ⟨by omega,ha⟩
      · rintro ⟨hi,hm⟩
        exact ⟨i+1,⟨hm,by omega⟩,by omega⟩
    rw [hold]
    cases x <;> simp
  have shiftBound (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) :
      ∀ i ∈ shifted s, i < R := by
    intro i hi
    rcases (shiftMem s hs i).mp hi with h | h <;> omega
  let t := shifted s
  let ell := R - pastLast s
  let fresh : ℕ × ℕ := (R-ell-2,R-1)
  let closes : Prop := x = true ∧ 1 ≤ ell ∧ ell+2 ≤ R
  obtain ⟨hmR,hmi,hmm⟩ := lastProps s hs
  have ellR : ell ≤ R := Nat.sub_le _ _
  have ellEq : ell + pastLast s = R := Nat.sub_add_cancel hmR
  have tm (i : ℕ) : i ∈ t ↔ (i+1 < R ∧ i+1 ∈ s) ∨
      (i = R-1 ∧ x = true) := shiftMem s hs i
  have tb : ∀ i ∈ t, i < R := shiftBound s hs
  have old (c : ℕ × ℕ) (hb : c.2 < R-1) :
      c ∈ candidates t R R ↔ (c.1+1,c.2+1) ∈ candidates s R R := by
    rw [cmem,cmem]
    simp only [Complete]
    constructor
    · rintro ⟨_,hlen,ha,hb',hz⟩
      have ha' := (tm c.1).mp ha
      have hb'' := (tm c.2).mp hb'
      refine ⟨by omega,by omega,?_,?_,?_⟩
      · rcases ha' with h | h
        · exact h.2
        · omega
      · rcases hb'' with h | h
        · exact h.2
        · omega
      · intro i hai hib his
        apply hz (i-1) (by omega) (by omega)
        apply (tm _).mpr
        left
        have he : i-1+1 = i := by omega
        simpa [he] using And.intro (hs i his) his
    · rintro ⟨_,hlen,ha,hb',hz⟩
      refine ⟨by omega,by omega,(tm _).mpr (Or.inl ⟨by omega,ha⟩),
        (tm _).mpr (Or.inl ⟨by omega,hb'⟩),?_⟩
      intro i hai hib hit
      rcases (tm i).mp hit with hi | hi
      · exact hz (i+1) (by omega) (by omega) hi.2
      · omega
  have newest (c : ℕ × ℕ) (hb : c.2 = R-1) :
      c ∈ candidates t R R ↔ closes ∧ c = fresh := by
    rw [cmem]
    constructor
    · rintro ⟨_,hlen,ha,hb',hz⟩
      have hx : x = true := by
        rcases (tm c.2).mp hb' with h | h
        · omega
        · exact h.2
      have has : c.1+1 ∈ s := by
        rcases (tm c.1).mp ha with h | h
        · exact h.2
        · omega
      have hlo := hmi _ has
      have he : pastLast s = c.1+2 := by
        by_contra hn
        have hp : 0 < pastLast s := by omega
        have hi := hmm hp
        have hz' := hz (pastLast s-2) (by omega) (by omega)
        apply hz'
        apply (tm _).mpr
        left
        have he' : pastLast s-2+1 = pastLast s-1 := by omega
        rw [he']
        exact ⟨by omega,hi⟩
      refine ⟨⟨hx,by omega,by omega⟩,?_⟩
      apply Prod.ext <;> dsimp [fresh] <;> omega
    · rintro ⟨⟨hx,hl,hr⟩,rfl⟩
      have hp : 0 < pastLast s := by omega
      have hi := hmm hp
      have he : fresh.1+1 = pastLast s-1 := by dsimp [fresh]; omega
      refine ⟨by dsimp [fresh]; omega,?_,?_,?_,?_⟩
      · dsimp [fresh]; omega
      · apply (tm _).mpr
        left
        rw [he]
        exact ⟨by omega,hi⟩
      · exact (tm _).mpr (Or.inr ⟨rfl,hx⟩)
      · intro i hai hib hit
        rcases (tm i).mp hit with hi' | hi'
        · have := hmi _ hi'.2
          dsimp [fresh] at hai hib
          omega
        · dsimp [fresh] at hib
          omega
  have allCandidates (c : ℕ × ℕ) :
      c ∈ candidates t R R ↔
        (c.2 < R-1 ∧ (c.1+1,c.2+1) ∈ candidates s R R) ∨
        (closes ∧ c = fresh) := by
    constructor
    · intro hc
      have hb := (cmem t c).mp hc
      by_cases he : c.2 = R-1
      · exact Or.inr ((newest c he).mp hc)
      · have hh : c.2 < R-1 := by omega
        exact Or.inl ⟨hh,(old c hh).mp hc⟩
    · rintro (⟨hb,hc⟩ | ⟨hc,rfl⟩)
      · exact (old c hb).mpr hc
      · exact (newest fresh rfl).mpr ⟨hc,rfl⟩
  have suffix : R - pastLast t = if x then 0 else min R (ell+1) := by
    have ht : pastLast t = if x then R else pastLast s-1 := by
      cases hx : x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        apply le_antisymm
        · apply Finset.sup_le
          intro i hi
          rcases (tm i).mp hi with hi | hi
          · have := hmi _ hi.2
            omega
          · simp [hx] at hi
        · by_cases hp : 1 < pastLast s
          · have hi := hmm (by omega)
            have hm : pastLast s-2 ∈ t := by
              apply (tm _).mpr
              left
              have he : pastLast s-2+1 = pastLast s-1 := by omega
              rw [he]
              exact ⟨by omega,hi⟩
            have hle := Finset.le_sup (f := fun i : ℕ => i+1) hm
            change pastLast s-2+1 ≤ pastLast t at hle
            omega
          · omega
      · have htR := (lastProps t tb).1
        have hm : R-1 ∈ t := (tm _).mpr (Or.inr ⟨rfl,hx⟩)
        have hle := Finset.le_sup (f := fun i : ℕ => i+1) hm
        change R-1+1 ≤ pastLast t at hle
        simp only [↓reduceIte]
        omega
    rw [ht]
    cases x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have phaseShift (b : ℕ) (hb : 0 < b) (hbR : b < R) :
      phase R t (b-1) = xor (phase R s b) (!x) := by
    let z := (Finset.Ioo b R).filter fun i => i ∉ s
    let zi := z.image fun i => i-1
    have zim (i : ℕ) : i ∈ zi ↔ b-1 < i ∧ i < R-1 ∧ i+1 ∉ s := by
      simp only [zi,z,Finset.mem_image,Finset.mem_filter,Finset.mem_Ioo]
      constructor
      · rintro ⟨a,⟨⟨hba,haR⟩,has⟩,hai⟩
        have he : i+1 = a := by omega
        exact ⟨by omega,by omega,by simpa [he] using has⟩
      · rintro ⟨hbi,hiR,his⟩
        exact ⟨i+1,⟨⟨by omega,by omega⟩,his⟩,by omega⟩
    have ze : (Finset.Ioo (b-1) R).filter (fun i => i ∉ t) =
        if x then zi else insert (R-1) zi := by
      ext i
      have lhs : i ∈ (Finset.Ioo (b-1) R).filter (fun i => i ∉ t) ↔
          (i ∈ zi ∨ (i = R-1 ∧ x = false)) := by
        simp only [Finset.mem_filter,Finset.mem_Ioo]
        constructor
        · rintro ⟨⟨hbi,hiR⟩,hit⟩
          by_cases hi : i < R-1
          · left
            apply (zim i).mpr
            refine ⟨hbi,hi,?_⟩
            intro his
            exact hit ((tm _).mpr (Or.inl ⟨by omega,his⟩))
          · right
            have he : i = R-1 := by omega
            refine ⟨he,?_⟩
            cases hx : x
            · rfl
            · exact (hit ((tm _).mpr (Or.inr ⟨he,hx⟩))).elim
        · rintro (hi | ⟨he,hx⟩)
          · obtain ⟨hbi,hiR,his⟩ := (zim i).mp hi
            refine ⟨⟨hbi,by omega⟩,?_⟩
            intro hit
            rcases (tm _).mp hit with h | h
            · exact his h.2
            · omega
          · subst i
            refine ⟨⟨by omega,by omega⟩,?_⟩
            intro hit
            rcases (tm _).mp hit with h | h
            · omega
            · simp [hx] at h
      rw [lhs]
      cases x <;> simp [or_comm]
    have zcard : zi.card = z.card := by
      apply Finset.card_image_of_injOn
      intro a ha b' hb' he
      have ha' := (Finset.mem_filter.mp ha).1
      have hb'' := (Finset.mem_filter.mp hb').1
      simp only [Finset.mem_Ioo] at ha' hb''
      dsimp at he
      omega
    have hn : R-1 ∉ zi := by simp [zim]
    have count : ((Finset.Ioo (b-1) R).filter fun i => i ∉ t).card =
        z.card + if x then 0 else 1 := by
      rw [ze]
      cases x <;> simp [hn,zcard]
    change decide (((Finset.Ioo (b-1) R).filter fun i => i ∉ t).card % 2 = 1) = _
    rw [count]
    change decide ((z.card + if x then 0 else 1) % 2 = 1) =
      xor (decide (z.card % 2 = 1)) (!x)
    have hm : z.card % 2 < 2 := Nat.mod_lt _ (by decide)
    cases x <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte,
      Nat.add_zero, Bool.xor_false, Bool.xor_true]
    by_cases he : z.card % 2 = 1
    · have hz : (z.card+1)%2 ≠ 1 := by omega
      simp [he,hz]
    · have hz : (z.card+1)%2 = 1 := by omega
      simp [he,hz]
  exact ⟨allCandidates,suffix,phaseShift⟩

/-- For every binary window, the prescribed state-only update gives its fresh
canonical state, and the same readout gives the original selector and rule. -/
theorem actual_window_update (R : ℕ) (hR : 1 ≤ R) (w : Fin R → Bool) (x : Bool) :
    memory (shiftWindow w x) = update R (memory w) x ∧
    readout R (memory w) = (selected (windowOnes w) R R,
      (selected (windowOnes w) R R).map (fun c => c.2+1), sharedRule R w) := by
  classical
  have cmem (s : Finset ℕ) (c : ℕ × ℕ) :
      c ∈ candidates s R R ↔ c.2 < R ∧ Complete s c.1 c.2 := by
    simp only [candidates, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨_,hb⟩,_,hc⟩
      exact ⟨hb,hc⟩
    · rintro ⟨hb,hc⟩
      exact ⟨⟨by have := hc.1; omega,hb⟩,by omega,hc⟩
  have ordered (s : Finset ℕ) (c d : ℕ × ℕ)
      (hc : c ∈ candidates s R R) (hd : d ∈ candidates s R R)
      (hcd : c.2 < d.2) : c.2 ≤ d.1 := by
    obtain ⟨_, _, _, hb, _⟩ := (cmem s c).mp hc
    obtain ⟨_, _, _, _, hz⟩ := (cmem s d).mp hd
    by_contra hn
    exact hz c.2 (by omega) hcd hb
  have sameEnd (s : Finset ℕ) (c d : ℕ × ℕ)
      (hc : c ∈ candidates s R R) (hd : d ∈ candidates s R R)
      (he : c.2 = d.2) : c = d := by
    obtain ⟨_, hcl, hca, _, hcz⟩ := (cmem s c).mp hc
    obtain ⟨_, hdl, hda, _, hdz⟩ := (cmem s d).mp hd
    have : c.1 = d.1 := by
      rcases lt_trichotomy c.1 d.1 with h | h | h
      · exact False.elim (hcz d.1 h (by omega) hda)
      · exact h
      · exact False.elim (hdz c.1 h (by omega) hca)
    exact Prod.ext this he
  let shifted := fun s : Finset ℕ => shiftOnes R s x
  have shiftMem (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) (i : ℕ) :
      i ∈ shifted s ↔ (i+1 < R ∧ i+1 ∈ s) ∨ (i = R-1 ∧ x = true) := by
    dsimp [shifted,shiftOnes]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    have hold : (∃ a, (a ∈ s ∧ 0 < a) ∧ a-1 = i) ↔ i+1 < R ∧ i+1 ∈ s := by
      constructor
      · rintro ⟨a, ⟨ha,hp⟩, he⟩
        have := hs a ha
        have : a = i+1 := by omega
        subst a
        exact ⟨by omega,ha⟩
      · rintro ⟨hi,hm⟩
        exact ⟨i+1,⟨hm,by omega⟩,by omega⟩
    rw [hold]
    cases x <;> simp
  have shiftBound (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) :
      ∀ i ∈ shifted s, i < R := by
    intro i hi
    rcases (shiftMem s hs i).mp hi with h | h <;> omega
  have recordMem (s : Finset ℕ) (r : (ℕ × ℕ) × Bool) :
      r ∈ (encode R s).1 ↔ r.1 ∈ undominated R s ∧ r.2 = phase R s r.1.2 := by
    simp only [encode, Finset.mem_image]
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨hc,rfl⟩
    · rintro ⟨hc,hp⟩
      exact ⟨r.1,hc,Prod.ext rfl hp.symm⟩
  have core (s : Finset ℕ) (hs : ∀ i ∈ s, i < R) :
      encode R (shifted s) = update R (encode R s) x := by
    let t := shifted s
    let ell := R - pastLast s
    let fresh : ℕ × ℕ := (R-ell-2,R-1)
    let closes : Prop := x = true ∧ 1 ≤ ell ∧ ell+2 ≤ R
    obtain ⟨allCandidates,suffix,phaseShift⟩ := actual_complete_runs_shift R hR s hs x
    change (∀ c : ℕ × ℕ, c ∈ candidates t R R ↔
      (c.2 < R-1 ∧ (c.1+1,c.2+1) ∈ candidates s R R) ∨
      (closes ∧ c = fresh)) at allCandidates
    have freshLength (hc : closes) : runLength fresh = ell := by
      dsimp [closes] at hc
      dsimp [runLength,fresh]
      omega
    have liftLength (c : ℕ × ℕ) : runLength (c.1+1,c.2+1) = runLength c := by
      dsimp [runLength]
      omega
    have frontier (c : ℕ × ℕ) : c ∈ undominated R t ↔
        (c.2 < R-1 ∧ (c.1+1,c.2+1) ∈ undominated R s ∧
          (closes → ell < runLength c)) ∨ (closes ∧ c = fresh) := by
      simp only [undominated, Finset.mem_filter]
      constructor
      · rintro ⟨hc,hu⟩
        rcases (allCandidates c).mp hc with ⟨hb,hc'⟩ | hf
        · left
          refine ⟨hb,⟨hc',?_⟩,?_⟩
          · intro d hd hcd
            have hod := ordered s (c.1+1,c.2+1) d hc' hd hcd
            have hdg := (cmem s d).mp hd
            let d' : ℕ × ℕ := (d.1-1,d.2-1)
            have dlift : (d'.1+1,d'.2+1) = d := by
              apply Prod.ext <;> dsimp [d'] <;> omega
            have dd : d' ∈ candidates t R R := by
              apply (allCandidates d').mpr
              left
              exact ⟨by dsimp [d']; omega,by rw [dlift]; exact hd⟩
            have hlt := hu d' dd (by dsimp [d']; omega)
            rw [← liftLength d',dlift] at hlt
            simpa only [liftLength] using hlt
          · intro hcl
            have hf := (allCandidates fresh).mpr (Or.inr ⟨hcl,rfl⟩)
            simpa only [freshLength hcl] using hu fresh hf hb
        · exact Or.inr hf
      · rintro (⟨hb,⟨hc,hu⟩,hf⟩ | ⟨hcl,rfl⟩)
        · refine ⟨(allCandidates c).mpr (Or.inl ⟨hb,hc⟩),?_⟩
          intro d hd hcd
          rcases (allCandidates d).mp hd with ⟨hdb,hd'⟩ | ⟨hcl,rfl⟩
          · simpa only [liftLength] using hu (d.1+1,d.2+1) hd' (by omega)
          · rw [freshLength hcl]
            exact hf hcl
        · refine ⟨(allCandidates fresh).mpr (Or.inr ⟨hcl,rfl⟩),?_⟩
          intro d hd hfd
          have hdg := (cmem t d).mp hd
          dsimp [fresh] at hfd
          omega
    have freshPhase : phase R t fresh.2 = false := by
      have he : Finset.Ioo (R-1) R = ∅ := by ext i; simp; omega
      simp [phase,transport,fresh,he]
    let survivors := ((encode R s).1.filter fun r => 0 < r.1.1).image
      (fun r => ((r.1.1-1,r.1.2-1),xor r.2 (!x)))
    have survMem (r : (ℕ × ℕ) × Bool) : r ∈ survivors ↔
        r.1.2 < R-1 ∧ (r.1.1+1,r.1.2+1) ∈ undominated R s ∧
        r.2 = phase R t r.1.2 := by
      simp only [survivors,Finset.mem_image,Finset.mem_filter,recordMem]
      constructor
      · rintro ⟨⟨⟨a,b⟩,eta⟩,⟨⟨hu,hp⟩,ha⟩,rfl⟩
        dsimp only at ha hp
        have hc := (Finset.mem_filter.mp hu).1
        obtain ⟨hbR,hlen,_,_,_⟩ := (cmem s (a,b)).mp hc
        have he : (a-1+1,b-1+1) = (a,b) := by apply Prod.ext <;> dsimp <;> omega
        refine ⟨by dsimp; omega,by simpa only [he] using hu,?_⟩
        dsimp at hp ⊢
        rw [hp,phaseShift b (by omega) hbR]
      · rintro ⟨hb,hu,hp⟩
        have hc := (Finset.mem_filter.mp hu).1
        have hg := (cmem s (r.1.1+1,r.1.2+1)).mp hc
        refine ⟨((r.1.1+1,r.1.2+1),phase R s (r.1.2+1)),
          ⟨⟨hu,rfl⟩,by simp⟩,?_⟩
        apply Prod.ext
        · simp
        · dsimp
          rw [← phaseShift (r.1.2+1) (by omega) hg.1]
          simpa using hp.symm
    apply Prod.ext
    · ext r
      have ur : (update R (encode R s) x).1 =
          (if closes then insert (fresh,false)
            (survivors.filter fun r => ell < runLength r.1) else survivors) := rfl
      rw [ur]
      rw [recordMem,frontier]
      by_cases hc : closes
      · rw [if_pos hc,Finset.mem_insert,Finset.mem_filter,survMem]
        constructor
        · rintro ⟨h,hp⟩
          rcases h with ⟨hb,hu,hl⟩ | ⟨_,he⟩
          · exact Or.inr ⟨⟨hb,hu,hp⟩,hl hc⟩
          · left
            apply Prod.ext he
            change r.2 = phase R t r.1.2 at hp
            rw [he,freshPhase] at hp
            exact hp
        · rintro (rfl | ⟨⟨hb,hu,hp⟩,hl⟩)
          · exact ⟨Or.inr ⟨hc,rfl⟩,freshPhase.symm⟩
          · exact ⟨Or.inl ⟨hb,hu,fun _ => hl⟩,hp⟩
      · rw [if_neg hc,survMem]
        simp only [hc,false_implies,and_true,false_and,or_false]
        tauto
    · exact suffix
  have wmem {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
      i.val ∈ windowOnes v ↔ v i = true := by
    simp only [windowOnes,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj,he⟩
      have : j = i := Fin.ext he
      simpa [this] using hj
    · intro hi; exact ⟨i,hi,rfl⟩
  have wb {n : ℕ} (v : Fin n → Bool) : ∀ i ∈ windowOnes v, i < n := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact j.isLt
  have ws : windowOnes (shiftWindow w x) = shifted (windowOnes w) := by
    ext i
    by_cases hi : i < R
    · rw [show i = (⟨i,hi⟩ : Fin R).val from rfl,wmem,shiftMem _ (wb w)]
      dsimp [shiftWindow]
      by_cases h : i+1 < R
      · rw [dif_pos h]
        have he := wmem w (⟨i+1,h⟩ : Fin R)
        dsimp at he
        have hn : i ≠ R-1 := by omega
        simp [h,hn,he]
      · rw [dif_neg h]
        have he : i = R-1 := by omega
        have hr : ¬ R-1+1 < R := by omega
        simp [he,hr]
    · constructor
      · intro hm; exact (hi (wb _ i hm)).elim
      · intro hm; exact (hi (shiftBound _ (wb w) i hm)).elim
  refine ⟨?_,?_⟩
  · change encode R (windowOnes (shiftWindow w x)) = _
    rw [ws]
    exact core (windowOnes w) (wb w)
  · let s := windowOnes w
    have scoreStrict (c d : ℕ × ℕ) (hc : c ∈ candidates s R R)
        (hd : d ∈ candidates s R R) (hne : c ≠ d)
        (hle : score R d ≤ score R c) : score R d < score R c := by
      have hcg := (cmem s c).mp hc
      have hdg := (cmem s d).mp hd
      have heq : score R d ≠ score R c := by
        intro he
        have hb : d.2 = c.2 := by
          have hm := congrArg (fun n => n % (R+1)) he
          simp only [score,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,
            Nat.zero_mod,Nat.zero_add,Nat.mod_mod] at hm
          rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hm
          exact hm
        exact hne ((sameEnd s d c hd hc hb).symm)
      omega
    cases hsel : selected s R R with
    | none =>
      have he : candidates s R R = ∅ := by
        simpa only [selected,List.argmax_eq_none,Finset.toList_eq_nil] using hsel
      have hu : undominated R s = ∅ := by simp [undominated,he]
      simp [memory,encode,readout,hu,sharedRule,direction,hsel,s]
    | some c =>
      obtain ⟨hcm,hmax,_⟩ := List.argmax_eq_some_iff.mp hsel
      have hc : c ∈ candidates s R R := Finset.mem_toList.mp hcm
      have hu : c ∈ undominated R s := by
        apply Finset.mem_filter.mpr
        refine ⟨hc,?_⟩
        intro d hd hcd
        have hle := hmax d (Finset.mem_toList.mpr hd)
        dsimp [score,runLength] at *
        nlinarith
      have hr : ((encode R s).1.toList.argmax (fun r => score R r.1)) =
          some (c,phase R s c.2) := by
        apply List.argmax_eq_some_iff.mpr
        have hm : (c,phase R s c.2) ∈ (encode R s).1 :=
          (recordMem s _).mpr ⟨hu,rfl⟩
        refine ⟨Finset.mem_toList.mpr hm,?_,?_⟩
        · intro d hd
          have hd' := (recordMem s d).mp (Finset.mem_toList.mp hd)
          exact hmax d.1 (Finset.mem_toList.mpr (Finset.mem_filter.mp hd'.1).1)
        · intro d hd hle
          have hd' := (recordMem s d).mp (Finset.mem_toList.mp hd)
          have hdc : d.1 = c := by
            by_contra hn
            have hlt := scoreStrict c d.1 hc (Finset.mem_filter.mp hd'.1).1
              (Ne.symm hn) (hmax d.1 (Finset.mem_toList.mpr (Finset.mem_filter.mp hd'.1).1))
            exact (not_lt_of_ge hle) hlt
          have he : d = (c,phase R s c.2) := Prod.ext hdc (by simpa [hdc] using hd'.2)
          subst d
          exact le_rfl
      change readout R (encode R s) = _
      simp only [readout,hr,Option.map_some]
      change (some c,some (c.2+1),phase R s c.2) =
        (some c,some (c.2+1),decide (direction s R R = 1))
      simp [hsel,direction,phase]

#print axioms actual_complete_runs_shift
#print axioms actual_window_update

end D5.S3.ObserverMemory.Trajectories.DominanceMemoryUpdate
