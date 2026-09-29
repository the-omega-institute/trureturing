/- GID: D5/S3/Combinatorics/Zigzag/EvenPaths
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/EvenPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit labelled reflection across the even antipodal boundary. -/

import D5.S3.Combinatorics.Zigzag.DecodedBalance
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

private noncomputable def evenTailReflection :
    (m : Nat) -> (s : State) -> EvenTail .positive m s ≃ EvenTail .negative m s
  | 0, _ => Equiv.refl _
  | m + 1, _ => Equiv.psigmaCongrRight fun i =>
      evenTailReflection m (stepTarget i)

/-- The explicit positive and negative labelled even tables are equivalent.
Corresponding entries retain their distinct labels rather than being collapsed
to their Laurent weights. -/
noncomputable def evenPathReflection (m : Nat) :
    EvenPath .positive m ≃ EvenPath .negative m := by
  exact Equiv.psigmaCongrRight fun i => evenTailReflection m (startTarget i)

private theorem evenTailReflection_charge (m : Nat) (s : State)
    (p : EvenTail .positive m s) :
    evenTailCharge (evenTailReflection m s p) = -evenTailCharge p := by
  induction m generalizing s with
  | zero =>
      change (evenTerminalValue (h := .negative) p).charge =
        -(evenTerminalValue (h := .positive) p).charge
      fin_cases s <;> fin_cases p <;> decide
  | succ m ih =>
      rcases p with ⟨i, p⟩
      rw [show evenTailReflection (m + 1) s ⟨i, p⟩ =
        ⟨i, evenTailReflection m (stepTarget i) p⟩ from rfl]
      simp only [evenTailCharge]
      have hstep : (stepValue (h := .negative) i).charge =
          -(stepValue (h := .positive) i).charge := by
        fin_cases s <;> fin_cases i <;> decide
      rw [hstep, ih]
      omega

/-- Reflection negates the complete even path charge, including the explicit
negative start, transition, and antipodal labels. -/
theorem evenPathReflection_charge (m : Nat) (p : EvenPath .positive m) :
    evenPathCharge (evenPathReflection m p) = -evenPathCharge p := by
  rcases p with ⟨i, p⟩
  rw [show evenPathReflection m ⟨i, p⟩ =
    ⟨i, evenTailReflection m (startTarget i) p⟩ from rfl]
  simp only [evenPathCharge]
  have hstart : (startValue (h := .negative) i).charge =
      -(startValue (h := .positive) i).charge := by
    fin_cases i <;> rfl
  rw [hstart, evenTailReflection_charge]
  omega

/-- Sector reflection restricts to zero-charge even paths. -/
noncomputable def evenZeroChargeReflection (m : Nat) :
    {p : EvenPath .positive m // evenPathCharge p = 0} ≃
      {p : EvenPath .negative m // evenPathCharge p = 0} :=
  Equiv.subtypeEquiv (evenPathReflection m) (by
    intro p
    rw [evenPathReflection_charge]
    omega)

private def lowAntipode : Form -> Int
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1 | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 0

private def highAntipode : Form -> Int
  | ⟨0, _⟩ => -1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1 | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 1

private theorem even_terminal_eval (r : Nat) (hr : 1 ≤ r)
    (h : Half) (s : State) (low high : Form) (q : Int) :
    let f := configurationFlow (3 * (2 * r)) h s (3 * r - 1) q +
      pairedFlow (3 * (2 * r)) (3 * r) low high
    f ((3 * r : Nat) - 1) = halfSign h * statePositive s +
        lowRetiredPositive low + highRetiredPositive high ∧
      f (1 - (3 * r : ZMod (3 * (2 * r)))) = halfSign h * stateNegative s +
        lowRetiredNegative low + highRetiredNegative high ∧
      f (3 * r : ZMod (3 * (2 * r))) = lowAntipode low + highAntipode high := by
  dsimp only
  have hinj := evenBoundaryVertex_injective r hr
  have hne (a b : Fin 6) (hab : a ≠ b) :
      evenBoundaryVertex r a ≠ evenBoundaryVertex r b := fun e => hab (hinj e)
  have hanti : ((3 * r : Nat) : ZMod (3 * (2 * r))) =
      -((3 * r : Nat) : ZMod (3 * (2 * r))) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have heq : 3 * r + 3 * r = 3 * (2 * r) := by omega
    rw [heq]
    exact ZMod.natCast_self (3 * (2 * r))
  have hanti' : (3 : ZMod (3 * (2 * r))) * r =
      -((3 : ZMod (3 * (2 * r))) * r) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hanti
  have hantiComm : (r : ZMod (3 * (2 * r))) * 3 =
      -((r : ZMod (3 * (2 * r))) * 3) := by simpa [mul_comm] using hanti'
  have hnegj : -((3 : ZMod (3 * (2 * r))) * r) =
      (3 : ZMod (3 * (2 * r))) * r := hanti'.symm
  have hjm : (((3 * r - 1 : Nat) : ZMod (3 * (2 * r)))) =
      (3 * r : ZMod (3 * (2 * r))) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hhigh : ((highClass (3 * (2 * r)) (3 * r) : Nat) :
      ZMod (3 * (2 * r))) = 1 - (3 * r : ZMod (3 * (2 * r))) := by
    unfold highClass
    have heq : 3 * (2 * r) + 1 - 3 * r = 3 * r + 1 := by omega
    rw [heq]; push_cast
    nth_rewrite 1 [hanti']
    ring
  have hhighSub : ((highClass (3 * (2 * r)) (3 * r) : ZMod (3 * (2 * r))) - 1) =
      (3 * r : ZMod (3 * (2 * r))) := by
    rw [hhigh]
    ring_nf
    simpa [mul_comm] using hnegj
  have honeHigh : 1 - (highClass (3 * (2 * r)) (3 * r) : ZMod (3 * (2 * r))) =
      (3 * r : ZMod (3 * (2 * r))) := by rw [hhigh]; ring
  have hnegHigh : -(highClass (3 * (2 * r)) (3 * r) : ZMod (3 * (2 * r))) =
      (3 * r : ZMod (3 * (2 * r))) - 1 := by rw [hhigh]; ring
  have hs := fun a b (hab : a ≠ b) => hne a b hab
  have h13 := hs 1 3 (by decide); have h23 := hs 2 3 (by decide)
  have h43 := hs 4 3 (by decide); have h53 := hs 5 3 (by decide)
  have h14 := hs 1 4 (by decide); have h24 := hs 2 4 (by decide)
  have h34 := hs 3 4 (by decide); have h54 := hs 5 4 (by decide)
  have h15 := hs 1 5 (by decide); have h25 := hs 2 5 (by decide)
  have h35 := hs 3 5 (by decide); have h45 := hs 4 5 (by decide)
  simp [evenBoundaryVertex] at h13 h23 h43 h53 h14 h24 h34 h54 h15 h25 h35 h45
  fin_cases low <;> fin_cases high <;>
    simp [configurationFlow, pairedFlow, edgeFlow, vertexFlow, formPair,
      lowRetiredPositive, highRetiredPositive, lowRetiredNegative,
      highRetiredNegative, lowAntipode, highAntipode, hjm, hnegj, hhigh,
      hhighSub, honeHigh, hnegHigh, h13, h23, h43, h53, h14, h24, h34,
      h54, h15, h25, h35, h45] <;> ring

private theorem even_terminal_local (h : Half) (s : State) (low high : Form)
    (hp : halfSign h * statePositive s + lowRetiredPositive low +
      highRetiredPositive high = 0)
    (hn : halfSign h * stateNegative s + lowRetiredNegative low +
      highRetiredNegative high = 0)
    (ha : lowAntipode low + highAntipode high = 0) :
    ∃ i : EvenTerminalIndex h s,
      low = (evenTerminalValue i).low ∧ high = (evenTerminalValue i).high := by
  fin_cases s <;> cases h <;> fin_cases low <;> fin_cases high
  all_goals simp_all [lowRetiredPositive, highRetiredPositive,
    lowRetiredNegative, highRetiredNegative, lowAntipode, highAntipode,
    halfSign, statePositive, stateNegative, State.A, State.D, State.E,
    State.H, State.I, EvenTerminalIndex, evenTerminalValue, Form.I, Form.II,
    Form.III, Form.IV, Form.V, Form.VI]

private theorem even_terminal_labels (r : Nat) (hr : 1 ≤ r)
    (h : Half) (s : State) (low high : Form) (q : Int)
    (hz : ∀ v : ZMod (3 * (2 * r)), v ≠ 0 ->
      (configurationFlow (3 * (2 * r)) h s (3 * r - 1) q +
        pairedFlow (3 * (2 * r)) (3 * r) low high) v = 0) :
    ∃ i : EvenTerminalIndex h s,
      low = (evenTerminalValue i).low ∧ high = (evenTerminalValue i).high := by
  have he := even_terminal_eval r hr h s low high q
  have hinj := evenBoundaryVertex_injective r hr
  have hne (a : Fin 6) (ha : a ≠ 0) : evenBoundaryVertex r a ≠ 0 := by
    intro e; exact ha (hinj (by simpa [evenBoundaryVertex] using e))
  exact even_terminal_local h s low high
    (he.1.symm.trans (by simpa [evenBoundaryVertex] using hz _ (hne 3 (by decide))))
    (he.2.1.symm.trans (by simpa [evenBoundaryVertex] using hz _ (hne 4 (by decide))))
    (he.2.2.symm.trans (by simpa [evenBoundaryVertex] using hz _ (hne 5 (by decide))))

private theorem even_tail_exists (r : Nat) (hr : 1 ≤ r) (h : Half)
    (F : Flow (3 * (2 * r)))
    (hz : ∀ v : ZMod (3 * (2 * r)), v ≠ 0 -> F v = 0) :
    ∀ (m : Nat) (s : State) (xs : List Form) (j : Nat) (q : Int),
      xs.length = 2 * m + 2 -> 3 ≤ j -> j + m = 3 * r ->
      F = configurationFlow (3 * (2 * r)) h s (j - 1) q +
        formsFlow (3 * (2 * r)) j xs ->
      ∃ p : EvenTail h m s,
        evenTailLowForms p ++ (evenTailHighForms p).reverse = xs
  | 0, s, xs, j, q, hlen, hj, hjr, hflow => by
      have hj' : j = 3 * r := by omega
      subst j
      cases xs with
      | nil => simp at hlen
      | cons low ys =>
          cases ys with
          | nil => simp at hlen
          | cons high zs =>
              have hzs : zs = [] := by simpa using hlen
              subst zs
              have hlast : 3 * r + 1 + ([] : List Form).length =
                  highClass (3 * (2 * r)) (3 * r) := by
                simp [highClass]
                omega
              have hpeel : formsFlow (3 * (2 * r)) (3 * r) [low, high] =
                  pairedFlow (3 * (2 * r)) (3 * r) low high := by
                simpa [formsFlow, highClass] using formsFlow_peel (3 * (2 * r)) (3 * r)
                  low high [] hlast
              have ht := even_terminal_labels r hr h s low high q (by
                intro v hv
                rw [hflow, hpeel] at hz
                exact hz v hv)
              rcases ht with ⟨i, rfl, rfl⟩
              exact ⟨i, by simp [evenTailLowForms, evenTailHighForms]⟩
  | m + 1, s, xs, j, q, hlen, hj, hjr, hflow => by
      cases xs with
      | nil => simp at hlen
      | cons low ys =>
          have hys : ys ≠ [] := by intro e; subst ys; simp at hlen
          let high := ys.getLast hys
          let inner := ys.dropLast
          have hdecomp : low :: (inner ++ [high]) = low :: ys := by
            congr
            exact List.dropLast_append_getLast hys
          have hinner : inner.length = 2 * m + 2 := by
            simp [inner, List.length_dropLast, hys] at hlen ⊢
            omega
          have hsep : 2 * j < 3 * (2 * r) := by omega
          have hinj := frontierVertex_injective (3 * (2 * r)) j hj hsep
          have hpeel : formsFlow (3 * (2 * r)) j (low :: (inner ++ [high])) =
              pairedFlow (3 * (2 * r)) j low high +
                formsFlow (3 * (2 * r)) (j + 1) inner :=
            formsFlow_peel _ _ _ _ _ (by unfold highClass; omega)
          have hbound : j + 1 + inner.length ≤ 3 * (2 * r) - j + 1 := by
            rw [hinner]
            omega
          have hfut := formsFlow_future_zero (3 * (2 * r)) j (j + 1) inner
            hj (by omega) hbound
          have hpos0 : ((j - 1 : Nat) : ZMod (3 * (2 * r))) ≠ 0 := by
            intro e
            have hd : 3 * (2 * r) ∣ j - 1 :=
              (ZMod.natCast_eq_zero_iff _ _).mp e
            have hle := Nat.le_of_dvd (by omega : 0 < j - 1) hd
            omega
          have hp0 :
              (configurationFlow (3 * (2 * r)) h s (j - 1) q +
                pairedFlow (3 * (2 * r)) j low high)
                ((j - 1 : Nat) : ZMod (3 * (2 * r))) = 0 := by
            have ht := hz _ hpos0
            rw [hflow, ← hdecomp, hpeel] at ht
            simpa [hfut.1, add_assoc] using ht
          have hn0 :
              (configurationFlow (3 * (2 * r)) h s (j - 1) q +
                pairedFlow (3 * (2 * r)) j low high)
                (-((j - 1 : Nat) : ZMod (3 * (2 * r)))) = 0 := by
            have ht := hz _ (neg_ne_zero.mpr hpos0)
            rw [hflow, ← hdecomp, hpeel] at ht
            simpa [hfut.2, add_assoc] using ht
          have hp : halfSign h * statePositive s + lowRetiredPositive low +
              highRetiredPositive high = 0 := by
            have hc : configurationFlow (3 * (2 * r)) h s (j - 1) q
                ((j - 1 : Nat) : ZMod (3 * (2 * r))) =
                halfSign h * statePositive s := by
              have hjm : (((j - 1 : Nat) : ZMod (3 * (2 * r)))) =
                  (j : ZMod (3 * (2 * r))) - 1 := by
                rw [Nat.cast_sub (by omega)]
                push_cast
                rfl
              have hne (a b : Fin 6) (hab : a ≠ b) :
                  frontierVertex (3 * (2 * r)) j a ≠
                    frontierVertex (3 * (2 * r)) j b := fun e => hab (hinj e)
              have h02 := hne 0 2 (by decide)
              have h12 := hne 1 2 (by decide)
              have h32 := hne 3 2 (by decide)
              simp [frontierVertex] at h02 h12 h32
              simp [configurationFlow, vertexFlow, hjm, h02, h12, h32]
            have he := pairedFlow_retiredPositive (3 * (2 * r)) j
              (by omega) (by omega) hinj low high
            simpa [hc, he, Pi.add_apply, add_assoc] using hp0
          have hn : halfSign h * stateNegative s + lowRetiredNegative low +
              highRetiredNegative high = 0 := by
            have hc : configurationFlow (3 * (2 * r)) h s (j - 1) q
                (-((j - 1 : Nat) : ZMod (3 * (2 * r)))) =
                halfSign h * stateNegative s := by
              have hjm : (((j - 1 : Nat) : ZMod (3 * (2 * r)))) =
                  (j : ZMod (3 * (2 * r))) - 1 := by
                rw [Nat.cast_sub (by omega)]
                push_cast
                rfl
              have hnegjm : (-((j - 1 : Nat) : ZMod (3 * (2 * r)))) =
                  1 - (j : ZMod (3 * (2 * r))) := by
                rw [hjm]
                ring
              have hne (a b : Fin 6) (hab : a ≠ b) :
                  frontierVertex (3 * (2 * r)) j a ≠
                    frontierVertex (3 * (2 * r)) j b := fun e => hab (hinj e)
              have h03 := hne 0 3 (by decide)
              have h13 := hne 1 3 (by decide)
              have h23 := hne 2 3 (by decide)
              simp [frontierVertex] at h03 h13 h23
              simp [configurationFlow, vertexFlow, hjm, hnegjm, h03, h13, h23]
            have he := pairedFlow_retiredNegative (3 * (2 * r)) j
              (by omega) (by omega) hinj low high
            simpa [hc, he, Pi.add_apply, add_assoc] using hn0
          rcases transition_labels_of_local_balance h s low high hp hn with
            ⟨i, hlow, hhigh⟩
          subst low
          rw [hhigh] at hdecomp hpeel hp0 hn0 hp hn
          have hnext : F = configurationFlow (3 * (2 * r)) h (stepTarget i) j
                (q + (stepValue (h := h) i).charge) +
              formsFlow (3 * (2 * r)) (j + 1) inner := by
            rw [hflow, ← hdecomp, hpeel, ← add_assoc,
              transition_flow (3 * (2 * r)) j (by omega) (by omega) h s i q]
            cases h <;> fin_cases s <;> fin_cases i <;> simp [stepValue]
          rcases even_tail_exists r hr h F hz m (stepTarget i) inner (j + 1)
            (q + (stepValue (h := h) i).charge) hinner (by omega) (by omega) hnext with
            ⟨p, hp⟩
          have htail : inner ++ [(stepValue (h := h) i).high] = ys :=
            (List.cons.inj hdecomp).2
          exact ⟨⟨i, p⟩, by
            simp only [evenTailLowForms, evenTailHighForms, List.reverse_cons,
              List.reverse_singleton]
            apply congrArg (List.cons (stepValue (h := h) i).low)
            exact calc
              evenTailLowForms p ++
                    ((evenTailHighForms p).reverse ++ [(stepValue (h := h) i).high]) =
                  (evenTailLowForms p ++ (evenTailHighForms p).reverse) ++
                    [(stepValue (h := h) i).high] := (List.append_assoc _ _ _).symm
              _ = inner ++ [(stepValue (h := h) i).high] :=
                congrArg (fun zs => zs ++ [(stepValue (h := h) i).high]) hp
              _ = ys := htail⟩

private theorem evenZeroPathChoices_surjective (r : Nat) (hr : 1 ≤ r) :
    Function.Surjective (evenZeroPathChoices r hr) := by
  rintro ⟨c, hc⟩
  have hlen : (choiceForms c).length = 3 * (2 * r) - 3 := by simp [choiceForms]
  cases hforms : choiceForms c with
  | nil => simp [hforms] at hlen; omega
  | cons f xs =>
      have hxs : xs.length = 2 * (3 * r - 3) + 2 := by
        rw [hforms] at hlen; simp at hlen; omega
      have hfirst : f = c.1 ⟨0, by omega⟩ := by
        have hh := congrArg (fun ys => ys[0]?) hforms
        simp [choiceForms, show 0 < 3 * (2 * r) - 3 by omega] at hh
        exact hh.symm
      have hf : f.allowedAtTwo := by
        rw [hfirst]; exact c.2 ⟨0, by omega⟩ rfl
      rcases start_classification (3 * (2 * r)) f hf with
        ⟨h, i, hlabel, hstart⟩
      have hflow : imbalance c =
          configurationFlow (3 * (2 * r)) h (startTarget i) 2
              (startValue i).charge + formsFlow (3 * (2 * r)) 3 xs := by
        rw [imbalance_eq_formsFlow, hforms]
        simp only [formsFlow]
        rw [hstart]
      rcases even_tail_exists r hr h (imbalance c) hc (3 * r - 3)
        (startTarget i) xs 3 (startValue i).charge hxs (by omega)
        (by omega) hflow with ⟨p, hp⟩
      let path : EvenPath h (3 * r - 3) := ⟨i, p⟩
      have hpf : evenPathForms path = choiceForms c := by
        rw [hforms]
        simp [path, evenPathForms, ← hlabel, hp]
      have hchoice : evenPathChoices r hr path = c := by
        apply Subtype.ext
        apply List.ofFn_injective
        have hencoded : choiceForms (evenPathChoices r hr path) =
            evenPathForms path := by
          apply List.ext_get
          · simp [choiceForms]
            omega
          · intro j hj hk
            simp [choiceForms, evenPathChoices]
            rfl
        simpa [choiceForms] using hencoded.trans hpf
      have hcharge : evenPathCharge path = 0 := by
        letI : NeZero (3 * (2 * r)) := ⟨by omega⟩
        letI : Fact (1 < 3 * (2 * r)) := ⟨by omega⟩
        letI : Fact (2 < 3 * (2 * r)) := ⟨by omega⟩
        have hboundary : ∀ v : ZMod (3 * (2 * r)), v ≠ 0 ->
            boundaryFlow (3 * (2 * r)) (evenPathCharge path) v = 0 := by
          intro v hv
          rw [← evenPathChoices_imbalance r hr path, hchoice]
          exact hc v hv
        have h := hboundary 1 (by exact one_ne_zero)
        simpa [boundaryFlow, vertexFlow, ZMod.neg_one_ne_one] using h
      cases h with
      | positive => exact ⟨Sum.inl ⟨path, hcharge⟩, Subtype.ext hchoice⟩
      | negative => exact ⟨Sum.inr ⟨path, hcharge⟩, Subtype.ext hchoice⟩

/-- Literal balanced choices of even parameter are exactly the two labelled
zero-charge antipodal path sectors. -/
noncomputable def evenBalancedChoicesEquiv (r : Nat) (hr : 1 ≤ r) :
    {c : Choices (2 * r) // Balanced c} ≃ EvenZeroPaths r :=
  (Equiv.ofBijective (evenZeroPathChoices r hr)
    ⟨evenZeroPathChoices_injective r hr, evenZeroPathChoices_surjective r hr⟩).symm

end D5.S3.Combinatorics.Zigzag
