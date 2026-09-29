/- GID: D5/S3/Combinatorics/Zigzag/OddPaths
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/OddPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit labelled reflection across the odd singleton boundary. -/

import D5.S3.Combinatorics.Zigzag.DecodedBalance
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

private noncomputable def oddTailReflection :
    (m : Nat) -> (s : State) -> OddTail .positive m s ≃ OddTail .negative m s
  | 0, _ => Equiv.refl _
  | m + 1, _ => Equiv.psigmaCongrRight fun i =>
      oddTailReflection m (stepTarget i)

/-- The explicit positive and negative labelled odd tables are equivalent,
including the distinct singleton labels `I, VI` and `V, III`. -/
noncomputable def oddPathReflection (m : Nat) :
    OddPath .positive m ≃ OddPath .negative m := by
  exact Equiv.psigmaCongrRight fun i => oddTailReflection m (startTarget i)

private theorem oddTailReflection_charge (m : Nat) (s : State)
    (p : OddTail .positive m s) :
    oddTailCharge (oddTailReflection m s p) = -oddTailCharge p := by
  induction m generalizing s with
  | zero =>
      change (oddTerminalValue (h := .negative) p).charge =
        -(oddTerminalValue (h := .positive) p).charge
      fin_cases s <;> fin_cases p <;> decide
  | succ m ih =>
      rcases p with ⟨i, p⟩
      rw [show oddTailReflection (m + 1) s ⟨i, p⟩ =
        ⟨i, oddTailReflection m (stepTarget i) p⟩ from rfl]
      simp only [oddTailCharge]
      have hstep : (stepValue (h := .negative) i).charge =
          -(stepValue (h := .positive) i).charge := by
        fin_cases s <;> fin_cases i <;> decide
      rw [hstep, ih]
      omega

/-- Reflection negates the complete odd path charge, with the singleton
terminal handled independently of the even antipode. -/
theorem oddPathReflection_charge (m : Nat) (p : OddPath .positive m) :
    oddPathCharge (oddPathReflection m p) = -oddPathCharge p := by
  rcases p with ⟨i, p⟩
  rw [show oddPathReflection m ⟨i, p⟩ =
    ⟨i, oddTailReflection m (startTarget i) p⟩ from rfl]
  simp only [oddPathCharge]
  have hstart : (startValue (h := .negative) i).charge =
      -(startValue (h := .positive) i).charge := by
    fin_cases i <;> rfl
  rw [hstart, oddTailReflection_charge]
  omega

/-- Sector reflection restricts to zero-charge odd paths. -/
noncomputable def oddZeroChargeReflection (m : Nat) :
    {p : OddPath .positive m // oddPathCharge p = 0} ≃
      {p : OddPath .negative m // oddPathCharge p = 0} :=
  Equiv.subtypeEquiv (oddPathReflection m) (by
    intro p
    rw [oddPathReflection_charge]
    omega)

private def singletonPositive (f : Form) : Int :=
  if f = Form.I then -1 else if f = Form.V then 1 else 0

private def singletonNegative (f : Form) : Int :=
  if f = Form.III then -1 else if f = Form.VI then 1 else 0

private theorem odd_terminal_eval (r : Nat) (hr : 1 ≤ r) (h : Half)
    (s : State) (label : Form) (q : Int) :
    let f := configurationFlow (3 * (2 * r + 1)) h s (3 * r + 1) q +
      edgeFlow (3 * (2 * r + 1)) (3 * r + 2) label
    f (3 * r + 1) = halfSign h * statePositive s + singletonPositive label ∧
      f (-((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1)))) =
        halfSign h * stateNegative s + singletonNegative label := by
  dsimp only
  letI : NeZero (3 * (2 * r + 1)) := ⟨by omega⟩
  have h10 : (1 : ZMod (3 * (2 * r + 1))) ≠ 0 := by
    intro e
    have hd := (ZMod.natCast_eq_zero_iff 1 (3 * (2 * r + 1))).mp e
    have hle := Nat.le_of_dvd (by omega : 0 < 1) hd
    omega
  have hinj := frontierVertex_injective (3 * (2 * r + 1)) (3 * r + 1)
    (by omega) (by omega)
  have hne (a b : Fin 6) (hab : a ≠ b) :
      frontierVertex (3 * (2 * r + 1)) (3 * r + 1) a ≠
        frontierVertex (3 * (2 * r + 1)) (3 * r + 1) b :=
    fun e => hab (hinj e)
  have h04 := hne 0 4 (by decide); have h14 := hne 1 4 (by decide)
  have h54 := hne 5 4 (by decide); have h05 := hne 0 5 (by decide)
  have h15 := hne 1 5 (by decide); have h45 := hne 4 5 (by decide)
  simp [frontierVertex] at h04 h14 h54 h05 h15 h45
  have hk : ((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) =
      -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have heq : 3 * r + 2 + (3 * r + 1) = 3 * (2 * r + 1) := by omega
    rw [heq]
    exact ZMod.natCast_self (3 * (2 * r + 1))
  have hksub : ((3 * r + 2 : ZMod (3 * (2 * r + 1))) - 1) =
      (3 * r + 1 : ZMod (3 * (2 * r + 1))) := by push_cast; ring
  have hone : (1 - (3 * r + 2 : ZMod (3 * (2 * r + 1)))) =
      -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by push_cast; ring
  have hneg : -((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) =
      ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := by rw [hk, neg_neg]
  have hplus' : (2 + (r : ZMod (3 * (2 * r + 1))) * 3) =
      (-1 - (r : ZMod (3 * (2 * r + 1))) * 3) := by
    calc
      _ = ((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) := by push_cast; ring
      _ = -((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := hk
      _ = _ := by push_cast; ring
  have hminus' : (-2 - (r : ZMod (3 * (2 * r + 1))) * 3) =
      (1 + (r : ZMod (3 * (2 * r + 1))) * 3) := by
    calc
      _ = -((3 * r + 2 : Nat) : ZMod (3 * (2 * r + 1))) := by push_cast; ring
      _ = ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) := hneg
      _ = _ := by push_cast; ring
  fin_cases label <;> simp [configurationFlow, edgeFlow, vertexFlow, formPair,
    singletonPositive, singletonNegative, hk, hksub, hone, hneg,
    hplus', hminus', h10, h04, h14, h54, h05, h15, h45,
    Form.I, Form.II, Form.III, Form.IV, Form.V, Form.VI] <;>
    simp_all [hplus', hminus'] <;> ring

private theorem odd_terminal_local (h : Half) (s : State) (label : Form)
    (hp : halfSign h * statePositive s + singletonPositive label = 0)
    (hn : halfSign h * stateNegative s + singletonNegative label = 0) :
    ∃ i : OddTerminalIndex h s, label = (oddTerminalValue i).label := by
  fin_cases s <;> cases h <;> fin_cases label
  all_goals simp_all [singletonPositive, singletonNegative, halfSign,
    statePositive, stateNegative, State.A, State.D, State.E, State.H, State.I,
    OddTerminalIndex, oddTerminalValue, Form.I, Form.II, Form.III, Form.IV,
    Form.V, Form.VI]

private theorem odd_terminal_labels (r : Nat) (hr : 1 ≤ r) (h : Half)
    (s : State) (label : Form) (q : Int)
    (hz : ∀ v : ZMod (3 * (2 * r + 1)), v ≠ 0 ->
      (configurationFlow (3 * (2 * r + 1)) h s (3 * r + 1) q +
        edgeFlow (3 * (2 * r + 1)) (3 * r + 2) label) v = 0) :
    ∃ i : OddTerminalIndex h s, label = (oddTerminalValue i).label := by
  have he := odd_terminal_eval r hr h s label q
  have hj0 : ((3 * r + 1 : Nat) : ZMod (3 * (2 * r + 1))) ≠ 0 := by
    intro e
    have hd := (ZMod.natCast_eq_zero_iff (3 * r + 1) (3 * (2 * r + 1))).mp e
    have hle := Nat.le_of_dvd (by omega : 0 < 3 * r + 1) hd
    omega
  apply odd_terminal_local h s label
  · rw [← he.1]
    convert hz _ hj0 using 1 <;> push_cast <;> ring
  · rw [← he.2]
    exact hz _ (neg_ne_zero.mpr hj0)

private theorem odd_tail_exists (r : Nat) (hr : 1 ≤ r) (h : Half)
    (F : Flow (3 * (2 * r + 1)))
    (hz : ∀ v : ZMod (3 * (2 * r + 1)), v ≠ 0 -> F v = 0) :
    ∀ (m : Nat) (s : State) (xs : List Form) (j : Nat) (q : Int),
      xs.length = 2 * m + 1 -> 3 ≤ j -> j + m = 3 * r + 2 ->
      F = configurationFlow (3 * (2 * r + 1)) h s (j - 1) q +
        formsFlow (3 * (2 * r + 1)) j xs ->
      ∃ p : OddTail h m s,
        oddTailLowForms p ++ (oddTailHighForms p).reverse = xs
  | 0, s, xs, j, q, hlen, hj, hjr, hflow => by
      have hj' : j = 3 * r + 2 := by omega
      subst j
      cases xs with
      | nil => simp at hlen
      | cons label ys =>
          have hys : ys = [] := by simpa using hlen
          subst ys
          have ht := odd_terminal_labels r hr h s label q (by
            intro v hv
            have hvF := hz v hv
            rw [hflow] at hvF
            simpa [formsFlow] using hvF)
          rcases ht with ⟨i, rfl⟩
          exact ⟨i, by simp [oddTailLowForms, oddTailHighForms]⟩
  | m + 1, s, xs, j, q, hlen, hj, hjr, hflow => by
      cases xs with
      | nil => simp at hlen
      | cons low ys =>
          have hys : ys ≠ [] := by intro e; subst ys; simp at hlen
          let high := ys.getLast hys
          let inner := ys.dropLast
          have hdecomp : low :: (inner ++ [high]) = low :: ys := by
            congr; exact List.dropLast_append_getLast hys
          have hinner : inner.length = 2 * m + 1 := by
            simp [inner, List.length_dropLast] at hlen ⊢; omega
          have hinj := frontierVertex_injective (3 * (2 * r + 1)) j hj (by omega)
          have hpeel := formsFlow_peel (3 * (2 * r + 1)) j low high inner
            (by unfold highClass; omega)
          have hbound : j + 1 + inner.length ≤ 3 * (2 * r + 1) - j + 1 := by
            rw [hinner]; omega
          have hfut := formsFlow_future_zero (3 * (2 * r + 1)) j (j + 1)
            inner hj (by omega) hbound
          have hpos0 : ((j - 1 : Nat) : ZMod (3 * (2 * r + 1))) ≠ 0 := by
            intro e
            have hd := (ZMod.natCast_eq_zero_iff (j - 1)
              (3 * (2 * r + 1))).mp e
            have hle := Nat.le_of_dvd (by omega : 0 < j - 1) hd
            omega
          have hp0 := hz _ hpos0
          have hn0 := hz _ (neg_ne_zero.mpr hpos0)
          rw [hflow, ← hdecomp, hpeel] at hp0 hn0
          have hp0' : (configurationFlow (3 * (2 * r + 1)) h s (j - 1) q +
              pairedFlow (3 * (2 * r + 1)) j low high)
                ((j - 1 : Nat) : ZMod (3 * (2 * r + 1))) = 0 := by
            simpa [hfut.1, add_assoc] using hp0
          have hn0' : (configurationFlow (3 * (2 * r + 1)) h s (j - 1) q +
              pairedFlow (3 * (2 * r + 1)) j low high)
                (-((j - 1 : Nat) : ZMod (3 * (2 * r + 1)))) = 0 := by
            simpa [hfut.2, add_assoc] using hn0
          have hp : halfSign h * statePositive s + lowRetiredPositive low +
              highRetiredPositive high = 0 := by
            have hc : configurationFlow (3 * (2 * r + 1)) h s (j - 1) q
                ((j - 1 : Nat) : ZMod (3 * (2 * r + 1))) =
                halfSign h * statePositive s := by
              have hjm : (((j - 1 : Nat) : ZMod (3 * (2 * r + 1)))) =
                  (j : ZMod (3 * (2 * r + 1))) - 1 := by
                rw [Nat.cast_sub (by omega)]
                push_cast
                rfl
              have hne (a b : Fin 6) (hab : a ≠ b) :
                  frontierVertex (3 * (2 * r + 1)) j a ≠
                    frontierVertex (3 * (2 * r + 1)) j b := fun e => hab (hinj e)
              have h02 := hne 0 2 (by decide)
              have h12 := hne 1 2 (by decide)
              have h32 := hne 3 2 (by decide)
              simp [frontierVertex] at h02 h12 h32
              simp [configurationFlow, vertexFlow, hjm, h02, h12, h32]
            have he := pairedFlow_retiredPositive _ j (by omega) (by omega) hinj low high
            simpa [hc, he, Pi.add_apply, add_assoc] using hp0'
          have hn : halfSign h * stateNegative s + lowRetiredNegative low +
              highRetiredNegative high = 0 := by
            have hc : configurationFlow (3 * (2 * r + 1)) h s (j - 1) q
                (-((j - 1 : Nat) : ZMod (3 * (2 * r + 1)))) =
                halfSign h * stateNegative s := by
              have hjm : (((j - 1 : Nat) : ZMod (3 * (2 * r + 1)))) =
                  (j : ZMod (3 * (2 * r + 1))) - 1 := by
                rw [Nat.cast_sub (by omega)]
                push_cast
                rfl
              have hnegjm : (-((j - 1 : Nat) : ZMod (3 * (2 * r + 1)))) =
                  1 - (j : ZMod (3 * (2 * r + 1))) := by
                rw [hjm]
                ring
              have hne (a b : Fin 6) (hab : a ≠ b) :
                  frontierVertex (3 * (2 * r + 1)) j a ≠
                    frontierVertex (3 * (2 * r + 1)) j b := fun e => hab (hinj e)
              have h03 := hne 0 3 (by decide)
              have h13 := hne 1 3 (by decide)
              have h23 := hne 2 3 (by decide)
              simp [frontierVertex] at h03 h13 h23
              simp [configurationFlow, vertexFlow, hjm, hnegjm, h03, h13, h23]
            have he := pairedFlow_retiredNegative _ j (by omega) (by omega) hinj low high
            simpa [hc, he, Pi.add_apply, add_assoc] using hn0'
          rcases transition_labels_of_local_balance h s low high hp hn with
            ⟨i, hlow, hhigh⟩
          subst low
          rw [hhigh] at hdecomp hpeel hp0 hn0 hp0' hn0' hp hn
          have hnext : F = configurationFlow (3 * (2 * r + 1)) h (stepTarget i) j
                (q + (stepValue (h := h) i).charge) +
              formsFlow (3 * (2 * r + 1)) (j + 1) inner := by
            rw [hflow, ← hdecomp, hpeel, ← add_assoc,
              transition_flow _ j (by omega) (by omega) h s i q]
            cases h <;> fin_cases s <;> fin_cases i <;>
              simp [stepValue]
          rcases odd_tail_exists r hr h F hz m (stepTarget i) inner (j + 1)
            (q + (stepValue (h := h) i).charge) hinner (by omega) (by omega) hnext with
            ⟨p, hp'⟩
          have htail : inner ++ [(stepValue (h := h) i).high] = ys :=
            (List.cons.inj hdecomp).2
          exact ⟨⟨i, p⟩, by
            simp only [oddTailLowForms, oddTailHighForms, List.reverse_cons]
            apply congrArg (List.cons (stepValue (h := h) i).low)
            exact calc
              oddTailLowForms p ++
                    ((oddTailHighForms p).reverse ++ [(stepValue (h := h) i).high]) =
                  (oddTailLowForms p ++ (oddTailHighForms p).reverse) ++
                    [(stepValue (h := h) i).high] := (List.append_assoc _ _ _).symm
              _ = inner ++ [(stepValue (h := h) i).high] :=
                congrArg (fun zs => zs ++ [(stepValue (h := h) i).high]) hp'
              _ = ys := htail⟩

private theorem oddZeroPathChoices_surjective (r : Nat) (hr : 1 ≤ r) :
    Function.Surjective (oddZeroPathChoices r hr) := by
  rintro ⟨c, hc⟩
  have hlen : (choiceForms c).length = 3 * (2 * r + 1) - 3 := by
    simp [choiceForms]
  cases hforms : choiceForms c with
  | nil => simp [hforms] at hlen; omega
  | cons f xs =>
      have hxs : xs.length = 2 * (3 * r - 1) + 1 := by
        rw [hforms] at hlen; simp at hlen; omega
      have hfirst : f = c.1 ⟨0, by omega⟩ := by
        have hh := congrArg (fun ys => ys[0]?) hforms
        simp [choiceForms, show 0 < 3 * (2 * r + 1) - 3 by omega] at hh
        exact hh.symm
      have hf : f.allowedAtTwo := by rw [hfirst]; exact c.2 ⟨0, by omega⟩ rfl
      rcases start_classification (3 * (2 * r + 1)) f hf with ⟨h, i, hl, hs⟩
      have hflow : imbalance c = configurationFlow (3 * (2 * r + 1)) h
          (startTarget i) 2 (startValue i).charge + formsFlow _ 3 xs := by
        rw [imbalance_eq_formsFlow, hforms]
        simp only [formsFlow]
        rw [hs]
      rcases odd_tail_exists r hr h (imbalance c) hc (3 * r - 1) (startTarget i)
        xs 3 (startValue i).charge hxs (by omega) (by omega) hflow with ⟨p, hp⟩
      let path : OddPath h (3 * r - 1) := ⟨i, p⟩
      have hpf : oddPathForms path = choiceForms c := by
        rw [hforms]; simp [path, oddPathForms, ← hl, hp]
      have hchoice : oddPathChoices r hr path = c := by
        apply Subtype.ext
        apply List.ofFn_injective
        have hencoded : choiceForms (oddPathChoices r hr path) = oddPathForms path := by
          apply List.ext_get
          · simp [choiceForms]
            omega
          · intro j hj hk
            simp [choiceForms, oddPathChoices]
            rfl
        simpa [choiceForms] using hencoded.trans hpf
      have hcharge : oddPathCharge path = 0 := by
        letI : NeZero (3 * (2 * r + 1)) := ⟨by omega⟩
        letI : Fact (1 < 3 * (2 * r + 1)) := ⟨by omega⟩
        letI : Fact (2 < 3 * (2 * r + 1)) := ⟨by omega⟩
        have hboundary : ∀ v : ZMod (3 * (2 * r + 1)), v ≠ 0 ->
            boundaryFlow (3 * (2 * r + 1)) (oddPathCharge path) v = 0 := by
          intro v hv
          rw [← oddPathChoices_imbalance r hr path, hchoice]
          exact hc v hv
        have h := hboundary 1 (by exact one_ne_zero)
        simpa [boundaryFlow, vertexFlow, ZMod.neg_one_ne_one] using h
      cases h with
      | positive => exact ⟨Sum.inl ⟨path, hcharge⟩, Subtype.ext hchoice⟩
      | negative => exact ⟨Sum.inr ⟨path, hcharge⟩, Subtype.ext hchoice⟩

/-- Literal balanced choices of odd parameter are exactly the two labelled
zero-charge singleton path sectors. -/
noncomputable def oddBalancedChoicesEquiv (r : Nat) (hr : 1 ≤ r) :
    {c : Choices (2 * r + 1) // Balanced c} ≃ OddZeroPaths r :=
  (Equiv.ofBijective (oddZeroPathChoices r hr)
    ⟨oddZeroPathChoices_injective r hr, oddZeroPathChoices_surjective r hr⟩).symm

end D5.S3.Combinatorics.Zigzag
