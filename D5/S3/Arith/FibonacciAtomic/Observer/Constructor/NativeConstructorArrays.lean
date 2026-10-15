/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact native constructor arrays, deterministic inverse bijections and distinct finite menus. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeDepthPatterns (Pattern Frontier fill)
open NativeWholeRowService (decodePattern)

/-- Exactly the six ordered pairs of the native constructor alphabet. -/
def Allowed : Reply → Reply → Prop
  | .branch, .alpha | .branch, .beta | .branch, .branch => True
  | .alpha, .absent | .beta, .absent | .absent, .absent => True
  | _, _ => False

/-- The depth-zero auxiliary carrier fixes the two cutoff children to alpha. -/
def Canonical : Nat → Source → Prop
  | 0, t => t = .of true
  | _ + 1, .of _ => True
  | d + 1, .mul l r => Canonical d l ∧ Canonical d r

/-- Independent local consistency; no matching-tree premise occurs. -/
def Edges (d : Nat) (z : Address → Reply) (a : Address) : Prop :=
  ∀ (w : Address) (b : Bool), w.length + 1 < d →
    Allowed (z (a ++ w)) (z (a ++ w ++ [b]))

/-- The existing native pattern parser, filled by the fixed cutoff alpha. -/
def realize (d : Nat) (z : Address → Reply) (a : Address) : Source :=
  fill (decodePattern z d a) (fun _ => .of true)

private theorem realize_succ (d : Nat) (z : Address → Reply) (a : Address) :
    realize (d+1) z a = match z a with
      | .alpha => .of true
      | .beta | .absent => .of false
      | .branch => .mul (realize d z (a ++ [false])) (realize d z (a ++ [true])) := by
  unfold realize
  rw [decodePattern]
  cases z a <;> rfl

private theorem absent_descendants (d : Nat) (z : Address → Reply)
    (a : Address) (edges : Edges d z a) (root : z a ≠ .branch)
    (w : Address) (nonempty : w ≠ []) (bound : w.length < d) :
    z (a ++ w) = .absent := by
  induction w generalizing a d with
  | nil => exact (nonempty rfl).elim
  | cons b w ih =>
      have e := edges [] b (by simp at bound ⊢; omega)
      have child : z (a ++ [b]) = .absent := by
        simp only [List.append_nil] at e
        cases h : z a <;> cases h' : z (a ++ [b]) <;> simp_all [Allowed]
      cases w with
      | nil => exact child
      | cons c w =>
          have shifted : Edges (d-1) z (a ++ [b]) := by
            intro v s hv
            have := edges (b :: v) s (by simp; omega)
            simpa [List.append_assoc] using this
          have h := ih (d-1) (a ++ [b]) shifted (by simp [child])
            (by simp) (by simp at bound ⊢; omega)
          simpa [List.append_assoc] using h

/-- Every independently legal bounded array has its literal canonical native
realization, including cutoff branches and all descendants of early leaves. -/
theorem legal_realization (d : Nat) (z : Address → Reply) (a : Address)
    (edges : Edges d z a) (root : 0 < d → z a ≠ .absent) :
    Canonical d (realize d z a) ∧
      ∀ w : Address, w.length < d → readout w (realize d z a) = z (a ++ w) := by
  induction d generalizing a with
  | zero => simp [realize, decodePattern, fill, Canonical]
  | succ d ih =>
      have shift (b : Bool) : Edges d z (a ++ [b]) := by
        intro w s hw
        have := edges (b :: w) s (by simp; omega)
        simpa [List.append_assoc] using this
      cases h : z a with
      | absent => exact (root (by omega) h).elim
      | alpha =>
          refine ⟨by simp [realize_succ, h, Canonical], ?_⟩
          intro w hw
          cases w with
          | nil => simp [realize_succ, h, readout]
          | cons b w =>
              have hz := absent_descendants (d+1) z a edges (by simp [h])
                (b :: w) (by simp) hw
              simpa [realize_succ, h, readout] using hz.symm
      | beta =>
          refine ⟨by simp [realize_succ, h, Canonical], ?_⟩
          intro w hw
          cases w with
          | nil => simp [realize_succ, h, readout]
          | cons b w =>
              have hz := absent_descendants (d+1) z a edges (by simp [h])
                (b :: w) (by simp) hw
              simpa [realize_succ, h, readout] using hz.symm
      | branch =>
          have childroot (b : Bool) : 0 < d → z (a ++ [b]) ≠ .absent := by
            intro hd
            have e := edges [] b (by simp; omega)
            simp only [List.append_nil, h] at e
            cases hc : z (a ++ [b]) <;> simp_all [Allowed]
          have left := ih (a ++ [false]) (shift false) (childroot false)
          have right := ih (a ++ [true]) (shift true) (childroot true)
          refine ⟨?_, ?_⟩
          · simpa [realize_succ, h, Canonical] using And.intro left.1 right.1
          · intro w hw
            cases w with
            | nil => simp [realize_succ, h, readout]
            | cons b w =>
                have hw' : w.length < d := by simpa using hw
                cases b
                · simpa [realize_succ, h, readout, List.append_assoc]
                    using left.2 w hw'
                · simpa [realize_succ, h, readout, List.append_assoc]
                    using right.2 w hw'

/-- The literal represented menu, including root and all words shorter than d. -/
abbrev W (d : Nat) := {w : Address // w.length < d}

instance (d : Nat) : Fintype (W d) :=
  Fintype.ofFinset (NativeWholeRowService.prefixAddresses d).toFinset
    (by intro w; simp only [List.mem_toFinset]; exact NativeWholeRowService.prefix_addresses_member d w)

/-- Total extension only supplies irrelevant replies outside the finite menu. -/
def extend {d : Nat} (z : W d → Reply) (w : Address) : Reply :=
  if h : w.length < d then z ⟨w,h⟩ else .absent

/-- Root nonabsence and the independent six-pair constraints on the exact menu. -/
def H (d : Nat) := {z : W d → Reply //
  extend z [] ≠ .absent ∧ Edges d (extend z) []}

/-- Native trees in the exact recursive carrier, rather than a height bound. -/
def S (d : Nat) := {t : Source // Canonical d t}

private theorem native_allowed (t : Source) (w : Address) (b : Bool) :
    Allowed (readout w t) (readout (w ++ [b]) t) := by
  induction w generalizing t with
  | nil => cases t with
    | of c => cases c <;> simp [readout, Allowed]
    | mul l r =>
        cases b
        · cases l with
          | of c => cases c <;> trivial
          | mul u v => trivial
        · cases r with
          | of c => cases c <;> trivial
          | mul u v => trivial
  | cons c w ih => cases t with
    | of c => simp [readout, Allowed]
    | mul l r => cases c <;> simpa only [readout, List.cons_append] using ih _

private theorem native_legal (d : Nat) (hd : 0 < d) (t : Source) :
    extend (fun w : W d => readout w.val t) [] ≠ .absent ∧
      Edges d (extend (fun w : W d => readout w.val t)) [] := by
  constructor
  · simp only [extend, List.length_nil, hd, dite_true]
    cases t with
    | of b => cases b <;> simp [readout]
    | mul l r => simp [readout]
  · intro w b bound
    have hw : w.length < d := by omega
    simpa [extend, hw, show w.length + 1 < d from bound] using native_allowed t w b

private theorem canonical_unique (d : Nat) (t u : Source)
    (ht : Canonical d t) (hu : Canonical d u)
    (same : ∀ w : Address, w.length < d → readout w t = readout w u) : t = u := by
  induction d generalizing t u with
  | zero => exact ht.trans hu.symm
  | succ d ih =>
      have root := same [] (by simp)
      cases t with
      | of b => cases u with
        | of c => cases b <;> cases c <;> simp_all [readout]
        | mul l r => cases b <;> simp [readout] at root
      | mul l r => cases u with
        | of c => cases c <;> simp [readout] at root
        | mul l' r' =>
            have left := ih l l' ht.1 hu.1 (fun w hw => same (false :: w) (by simp; omega))
            have right := ih r r' ht.2 hu.2 (fun w hw => same (true :: w) (by simp; omega))
            exact congrArg₂ FreeMagma.mul left right

/-- Literal scalar readout; the codomain legality is independent of its realization. -/
def scalarReadout (d : Nat) (hd : 0 < d) (t : S d) : H d :=
  ⟨fun w => readout w.val t.val, native_legal d hd t.val⟩

/-- A deterministic inverse, with alpha frontier filling and no selection. -/
def scalarReconstruct (d : Nat) (z : H d) : S d :=
  ⟨realize d (extend z.val) [],
    (legal_realization d (extend z.val) [] z.property.2 (fun _ => z.property.1)).1⟩

private theorem scalar_left_inverse (d : Nat) (hd : 0 < d) :
    Function.LeftInverse (scalarReconstruct d) (scalarReadout d hd) := by
  intro t
  apply Subtype.ext
  apply canonical_unique d _ _ (scalarReconstruct d (scalarReadout d hd t)).property t.property
  intro w hw
  have h := (legal_realization d (extend (scalarReadout d hd t).val) []
    (scalarReadout d hd t).property.2 (fun _ => (scalarReadout d hd t).property.1)).2 w hw
  simpa [scalarReconstruct, scalarReadout, extend, hw] using h

private theorem scalar_right_inverse (d : Nat) (hd : 0 < d) :
    Function.RightInverse (scalarReconstruct d) (scalarReadout d hd) := by
  intro z
  apply Subtype.ext
  funext w
  have h := (legal_realization d (extend z.val) [] z.property.2 (fun _ => z.property.1)).2 w.val w.property
  simpa [scalarReadout, scalarReconstruct, extend, w.property] using h

/-- The exact scalar bijection is the original-root literal reply function. -/
def scalarEquiv (d : Nat) (hd : 0 < d) : S d ≃ H d where
  toFun := scalarReadout d hd
  invFun := scalarReconstruct d
  left_inv := scalar_left_inverse d hd
  right_inv := scalar_right_inverse d hd

/-- Products retain all correlations and use the same deterministic scalar inverse. -/
def productEquiv (d n : Nat) (hd : 0 < d) : (Fin n → S d) ≃ (Fin n → H d) where
  toFun x i := scalarEquiv d hd (x i)
  invFun z i := (scalarEquiv d hd).symm (z i)
  left_inv x := funext (fun i => (scalarEquiv d hd).left_inv (x i))
  right_inv z := funext (fun i => (scalarEquiv d hd).right_inv (z i))

private theorem prefix_nodup (d : Nat) : (NativeWholeRowService.prefixAddresses d).Nodup := by
  induction d with
  | zero => simp [NativeWholeRowService.prefixAddresses]
  | succ d ih =>
      simp only [NativeWholeRowService.prefixAddresses, List.singleton_append]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · apply List.nodup_append.mpr
        refine ⟨ih.map (by intro a b h; exact List.cons.inj h |>.2),
          ih.map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩
        intro a ha b hb hab
        obtain ⟨u, _, hu⟩ := List.mem_map.mp ha
        obtain ⟨v, _, hv⟩ := List.mem_map.mp hb
        rw [← hu, ← hv] at hab
        cases hab

/-- The complete constructor representation, including exact carriers, the
literal scalar and product bijections, and the number of distinct coordinates. -/
theorem faithful_constructor_representation (d n : Nat) (hd : 0 < d) (hn : 0 < n) :
    (∀ t : Source, Canonical 1 t ↔
      t = .of true ∨ t = .of false ∨ t = .mul (.of true) (.of true)) ∧
    (∀ (k : Nat) (l r : Source), Canonical (k+1) (.mul l r) ↔
      Canonical k l ∧ Canonical k r) ∧
    Function.Bijective (scalarReadout d hd) ∧
    Function.Bijective (productEquiv d n hd) ∧
    (∀ (x : Fin n → S d) (i : Fin n) (w : W d),
      (productEquiv d n hd x i).val w = readout w.val (x i).val) ∧
    Fintype.card (Fin n × W d) = n * (2^d-1) ∧ Fintype.card Reply = 4 := by
  refine ⟨?_, ?_, (scalarEquiv d hd).bijective, (productEquiv d n hd).bijective,
    (by intros; rfl), ?_, ?_⟩
  · intro t
    cases t with
    | of b => cases b <;> simp [Canonical]
    | mul l r =>
        simp only [Canonical]; simp only [FreeMagma.mul_eq]
        constructor
        · rintro ⟨rfl,rfl⟩; exact Or.inr (Or.inr rfl)
        · intro h
          rcases h with h | h | h
          · cases h
          · cases h
          · injection h with hl hr
            exact ⟨hl,hr⟩
  · intros; rfl
  · have count : Fintype.card (W d) = 2^d-1 := by
      calc
        Fintype.card (W d) = (NativeWholeRowService.prefixAddresses d).toFinset.card :=
          @Fintype.card_of_finset' Address {w : Address | w.length < d}
            (NativeWholeRowService.prefixAddresses d).toFinset
            (by
              intro w
              simp only [List.mem_toFinset]
              exact NativeWholeRowService.prefix_addresses_member d w)
            (inferInstanceAs (Fintype (W d)))
        _ = 2^d-1 := by
          rw [List.toFinset_card_of_nodup (prefix_nodup d)]
          exact NativeWholeRowService.prefix_addresses_count d
    simp [Fintype.card_prod, count]
  · decide

#print axioms legal_realization
#print axioms faithful_constructor_representation

end D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays
