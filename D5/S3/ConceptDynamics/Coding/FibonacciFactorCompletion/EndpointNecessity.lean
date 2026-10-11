/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed actual tails force the complete indexed endpoint budget in Q(t). -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open scoped Topology

/-- One actual legal extension of a fixed literal, scalar and guard tail.
Only departures before the color-word length are constrained. -/
def ClosedOriginalTailExtension (b : ℝ) (A : List Label) (cs : List Color)
    (ξ : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard) : Prop :=
  ∃ (a : ℕ → Label) (X : ℕ → ℝ) (q : ℕ → Guard),
    q 0 = .G0 ∧
    (∀ p, nextGuard (q p) (a p) = some (q (p+1))) ∧
    (∀ p, InSupport (q p) (X p)) ∧
    (∀ p, X p = branch (a p) (X (p+1))) ∧
    (∀ p (hp : p < A.length), a p = A[p]) ∧
    (∀ p, a (A.length+p) = ξ p ∧ X (A.length+p) = x p ∧
      q (A.length+p) = path p) ∧
    (∀ r (hr : r < cs.length), ClosedExpanded b cs[r] (X r))

private theorem endpoint_extension_slots (b : ℝ) (A : List Label) (cs : List Color)
    (hlen : A.length = cs.length) (ξ : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (h : ClosedOriginalTailExtension b A cs ξ x path) :
    ∀ r (hr : r < cs.length), ClosedExpanded b cs[r] (compose (A.drop r) (x 0)) := by
  obtain ⟨a,X,q,hq,edges,support,recurrence,prefixLabels,future,slots⟩ := h
  have terminal : X A.length = x 0 := by simpa using (future 0).2.1
  have coordinates := prefix_coordinates A a X (x 0) prefixLabels recurrence terminal
  intro r hr
  have hrA : r ≤ A.length := by omega
  rw [← coordinates r hrA]
  exact slots r hr

private theorem endpoint_choice_append (R : Bool → List Label) (xs ys : List Bool) :
    choiceBlocks R (xs ++ ys) = choiceBlocks R xs ++ choiceBlocks R ys := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.cons_append,choiceBlocks,ih,List.append_assoc]

private theorem endpoint_closed_preimage (b : ℝ) (c : Color) (w : List Label) :
    IsClosed {z : ℝ | ClosedExpanded b c (compose w z)} ∧
      {z : ℝ | ClosedExpanded b c (compose w z)}.OrdConnected := by
  have affine (z : ℝ) : compose w z = compose w 0 + (-g)^w.length*z := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 z
  have continuous : Continuous (compose w) := by
    have heq : compose w = fun z : ℝ => compose w 0 + (-g)^w.length*z := funext affine
    rw [heq]
    fun_prop
  have closed : IsClosed {z : ℝ | ClosedExpanded b c (compose w z)} := by
    change IsClosed ({z : ℝ | compose w z ∈ Set.Icc (-1) phi} ∩
      {z : ℝ | compose w z ∈ Set.Icc (cut c.val-b) (cut (c.val+1)+b)})
    exact (isClosed_Icc.preimage continuous).inter (isClosed_Icc.preimage continuous)
  have interval : {z : ℝ | ClosedExpanded b c z}.OrdConnected := by
    refine ⟨?_⟩
    intro x hx y hy z hz
    exact ⟨⟨hx.1.1.trans hz.1,hz.2.trans hy.1.2⟩,
      hx.2.1.trans hz.1,hz.2.trans hy.2.2⟩
  refine ⟨closed,?_⟩
  by_cases hsign : 0 ≤ (-g)^w.length
  · apply interval.preimage_mono
    intro x y hxy
    rw [affine x,affine y]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hxy hsign) _
  · apply interval.preimage_anti
    intro x y hxy
    rw [affine x,affine y]
    exact add_le_add_right (mul_le_mul_of_nonpos_left hxy (le_of_not_ge hsign)) _

private theorem endpoint_period_fixed (s : Guard) (w : List Label) (y : ℝ)
    (hperiod : PeriodicTail s w y) : compose w y = y := by
  obtain ⟨a,x,path,h0,hx,edges,support,recurrence,prefixLabels,period⟩ := hperiod
  have terminal : x w.length = y := by simpa only [Nat.zero_add,hx] using (period 0).2.1
  have value := prefix_coordinates w a x y prefixLabels recurrence terminal 0 (Nat.zero_le _)
  simpa only [hx,List.drop_zero] using value.symm

/-- All approximations retain the supplied terminal scalar x, including x outside
its canonical hull. The endpoint is obtained through the existing signed criterion. -/
private theorem endpoint_period_closed (s : Guard) (R : Bool → List Label)
    (bs : List Bool) (y : ℝ) (hperiod : PeriodicTail s (choiceBlocks R bs) y)
    (hpositive : 0 < (choiceBlocks R bs).length)
    (b : ℝ) (c : Color) (w : List Label) (x : ℝ)
    (all : ∀ zs : List Bool,
      ClosedExpanded b c (compose w (compose (choiceBlocks R zs) x))) :
    ClosedExpanded b c (compose w y) := by
  let v := choiceBlocks R bs
  let a : ℝ := (-g)^v.length
  let T : Set ℝ := {z | ClosedExpanded b c (compose w z)}
  have slope := return_slope_control v.length hpositive
  have fixed : compose v y = y := endpoint_period_fixed s v y hperiod
  have affine (z : ℝ) : compose v z = y+a*(z-y) := by
    have h := literal_source_geometry.2.2.2.1 v y (z-y)
    have hz : y+(z-y) = z := by ring
    rw [hz,fixed] at h
    exact h
  have realize : ∀ n : ℕ, ∃ zs : List Bool,
      compose (choiceBlocks R zs) x = (compose v)^[n] x := by
    intro n
    induction n with
    | zero => exact ⟨[],rfl⟩
    | succ n ih =>
      obtain ⟨zs,hzs⟩ := ih
      refine ⟨bs ++ zs,?_⟩
      rw [endpoint_choice_append,literal_source_geometry.2.2.2.2,hzs]
      rw [Function.iterate_succ_apply']
  have orbit : ∀ n : ℕ, (fun z : ℝ => y+a*(z-y))^[n] x ∈ T := by
    intro n
    obtain ⟨zs,hzs⟩ := realize n
    have heq : compose v = fun z : ℝ => y+a*(z-y) := funext affine
    rw [← heq,← hzs]
    exact all zs
  have preimage := endpoint_closed_preimage b c w
  have conclusion := (competing_tail_orbit_criterion T preimage.2 a y
    slope.1 slope.2.1 slope.2.2).2.mp ⟨x,orbit⟩
  by_cases ha : 0 < a
  · have pair : T.Nonempty ∧ y ∈ closure T := by
      simpa only [if_pos ha] using conclusion
    have member := pair.2
    rw [preimage.1.closure_eq] at member
    exact member
  · simpa only [if_neg ha, T, Set.mem_setOf_eq] using conclusion

private theorem endpoint_both_closed (s : Guard) (R : Bool → List Label)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (R i).length = L)
    (hlegal : ∀ i, LegalWord s s (R i))
    (b : ℝ) (c : Color) (w : List Label) (x : ℝ)
    (all : ∀ zs : List Bool,
      ClosedExpanded b c (compose w (compose (choiceBlocks R zs) x))) :
    ClosedExpanded b c (compose w (canonicalReturnLo R L)) ∧
      ClosedExpanded b c (compose w (canonicalReturnHi R L)) := by
  obtain ⟨imin,imax,hmin,hmax,low,high⟩ := canonical_periodic_endpoints s R L hL hlen hlegal
  by_cases ha : 0 < (-g)^L
  · rw [if_pos ha] at low high
    constructor
    · apply endpoint_period_closed s R [imin] (canonicalReturnLo R L)
        (by simpa only [choiceBlocks,List.append_nil] using low)
        (by simpa only [choiceBlocks,List.append_nil,hlen] using hL) b c w x all
    · apply endpoint_period_closed s R [imax] (canonicalReturnHi R L)
        (by simpa only [choiceBlocks,List.append_nil] using high)
        (by simpa only [choiceBlocks,List.append_nil,hlen] using hL) b c w x all
  · rw [if_neg ha] at low high
    constructor
    · apply endpoint_period_closed s R [imin,imax] (canonicalReturnLo R L)
        (by simpa only [choiceBlocks,List.append_nil] using low)
        (by simp only [choiceBlocks,List.append_nil,List.length_append,hlen]; omega)
        b c w x all
    · apply endpoint_period_closed s R [imax,imin] (canonicalReturnHi R L)
        (by simpa only [choiceBlocks,List.append_nil] using high)
        (by simp only [choiceBlocks,List.append_nil,List.length_append,hlen]; omega)
        b c w x all

private theorem endpoint_component_necessary (b : ℝ) (hb : 0 ≤ b)
    (s : Guard) (P : List Label) (h : List Color) (hPlen : P.length = h.length)
    (R : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (R i).length = L)
    (hWlen : ∀ i, (W i).length = L) (hlegal : ∀ i, LegalWord s s (R i))
    (x : ℝ)
    (all : ∀ zs : List Bool, ∀ r (hr : r < (h ++ choiceBlocks W zs).length),
      ClosedExpanded b (h ++ choiceBlocks W zs)[r]
        (compose ((P ++ choiceBlocks R zs).drop r) x)) :
    EndpointCertificate b (canonicalReturnLo R L) (canonicalReturnHi R L) P h ∧
      ∀ i, EndpointCertificate b (canonicalReturnLo R L) (canonicalReturnHi R L) (R i) (W i) := by
  have stem : ∀ zs : List Bool, ∀ r (hr : r < h.length),
      ClosedExpanded b h[r] (compose (P.drop r) (compose (choiceBlocks R zs) x)) := by
    intro zs r hr
    have hwhole : r < (h ++ choiceBlocks W zs).length := by simp only [List.length_append]; omega
    have hrP : r ≤ P.length := by omega
    simpa only [List.getElem_append_left hr,List.drop_append_of_le_length hrP,
      literal_source_geometry.2.2.2.2] using all zs r hwhole
  have returns : ∀ i zs, ∀ r (hr : r < (W i).length),
      ClosedExpanded b (W i)[r] (compose ((R i).drop r) (compose (choiceBlocks R zs) x)) := by
    intro i zs r hr
    have hrR : r ≤ (R i).length := by rw [hlen]; have := hWlen i; omega
    have hwhole : P.length+r < (h ++ choiceBlocks W (i::zs)).length := by
      simp only [choiceBlocks,List.length_append]; omega
    have hcolor : (h ++ choiceBlocks W (i::zs))[P.length+r] = (W i)[r] := by
      simp only [choiceBlocks,hPlen,List.getElem_append_right (by omega : h.length ≤ h.length+r),
        Nat.add_sub_cancel_left,List.getElem_append_left hr]
    have hdrop : (P ++ choiceBlocks R (i::zs)).drop (P.length+r) =
        (R i).drop r ++ choiceBlocks R zs := by
      change (P ++ (R i ++ choiceBlocks R zs)).drop (P.length+r) = _
      rw [List.drop_append,List.drop_eq_nil_of_le (by omega : P.length ≤ P.length+r),
        List.nil_append,Nat.add_sub_cancel_left]
      exact List.drop_append_of_le_length hrR
    have hslot := all (i::zs) (P.length+r) hwhole
    rw [hcolor,hdrop,literal_source_geometry.2.2.2.2] at hslot
    exact hslot
  constructor
  · intro r hr
    have endpoints := endpoint_both_closed s R L hL hlen hlegal b h[r] (P.drop r) x
      (fun zs => stem zs r hr)
    exact ⟨(expanded_distance_formula b hb h[r] _).mp endpoints.1,
      (expanded_distance_formula b hb h[r] _).mp endpoints.2⟩
  · intro i r hr
    have endpoints := endpoint_both_closed s R L hL hlen hlegal b (W i)[r] ((R i).drop r) x
      (fun zs => returns i zs r hr)
    exact ⟨(expanded_distance_formula b hb (W i)[r] _).mp endpoints.1,
      (expanded_distance_formula b hb (W i)[r] _).mp endpoints.2⟩

private theorem endpoint_cost_le_of_certificate (b lo hi : ℝ) (w : List Label) (cs : List Color)
    (h : EndpointCertificate b lo hi w cs) : ∀ z ∈ endpointCosts lo hi w cs, z ≤ b := by
  intro z hz
  obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hz
  exact max_le (h r.val r.isLt).1.2 (h r.val r.isLt).2.2


private theorem endpoint_field_max (u v : ℝ)
    (hu : u ∈ coefficientField) (hv : v ∈ coefficientField) : max u v ∈ coefficientField := by
  rcases le_total u v with h | h
  · simpa only [max_eq_right h] using hv
  · simpa only [max_eq_left h] using hu

private theorem endpoint_field_constants :
    t ∈ coefficientField ∧ g ∈ coefficientField ∧ lam ∈ coefficientField ∧ phi ∈ coefficientField := by
  have ht : t ∈ coefficientField := fun F ht => ht
  have htwo : (2 : ℝ) ∈ coefficientField := by simpa using coefficientField.intCast_mem (2 : ℤ)
  have hten : (10 : ℝ) ∈ coefficientField := by simpa using coefficientField.intCast_mem (10 : ℤ)
  refine ⟨ht,?_,?_,?_⟩
  · exact coefficientField.sub_mem (coefficientField.mul_mem htwo ht) coefficientField.one_mem
  · exact coefficientField.div_mem (coefficientField.sub_mem coefficientField.one_mem ht) hten
  · exact coefficientField.add_mem coefficientField.one_mem ht

private theorem endpoint_compose_field (w : List Label) (x : ℝ)
    (hx : x ∈ coefficientField) : compose w x ∈ coefficientField := by
  have affine : compose w x = compose w 0 + (-g)^w.length*x := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 x
  rw [affine]
  exact coefficientField.add_mem (literal_coefficient_mem w)
    (coefficientField.mul_mem
      (coefficientField.pow_mem (coefficientField.neg_mem endpoint_field_constants.2.1) w.length) hx)

private theorem endpoint_cut_field (n : ℕ) : cut n ∈ coefficientField := by
  obtain ⟨ht,hg,hlam,hphi⟩ := endpoint_field_constants
  have hT2 : T2 ∈ coefficientField := coefficientField.sub_mem coefficientField.one_mem ht
  have hn (m : ℤ) : (m : ℝ) ∈ coefficientField := coefficientField.intCast_mem m
  rcases n with _ | n
  · exact coefficientField.neg_mem coefficientField.one_mem
  rcases n with _ | n
  · exact coefficientField.sub_mem (coefficientField.neg_mem hT2) hlam
  rcases n with _ | n
  · exact coefficientField.sub_mem hg (coefficientField.mul_mem (hn 3) hlam)
  rcases n with _ | n
  · exact coefficientField.sub_mem ht (coefficientField.mul_mem (hn 5) hlam)
  rcases n with _ | n
  · exact coefficientField.sub_mem (coefficientField.mul_mem (hn 2) ht)
      (coefficientField.mul_mem (hn 7) hlam)
  rcases n with _ | n
  · exact coefficientField.add_mem (coefficientField.mul_mem (hn 2) ht) hlam
  · exact hphi

private theorem endpoint_costs_field (lo hi : ℝ) (w : List Label) (cs : List Color)
    (hlo : lo ∈ coefficientField) (hhi : hi ∈ coefficientField) :
    ∀ z ∈ endpointCosts lo hi w cs, z ∈ coefficientField := by
  intro z hz
  obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hz
  have left := endpoint_compose_field (w.drop r.val) lo hlo
  have right := endpoint_compose_field (w.drop r.val) hi hhi
  have cutlo := endpoint_cut_field cs[r].val
  have cuthi := endpoint_cut_field (cs[r].val+1)
  exact endpoint_field_max _ _
    (endpoint_field_max _ _ (coefficientField.sub_mem cutlo left)
      (endpoint_field_max _ _ coefficientField.zero_mem (coefficientField.sub_mem left cuthi)))
    (endpoint_field_max _ _ (coefficientField.sub_mem cutlo right)
      (endpoint_field_max _ _ coefficientField.zero_mem (coefficientField.sub_mem right cuthi)))

private theorem endpoint_family_budget_field (P Q : List Label) (h : List Color)
    (U V : Bool → List Label) (W : Bool → List Color) (L : ℕ) :
    familyEndpointBudget P Q h U V W L ∈ coefficientField := by
  have hu := canonical_return_coefficient_mem U L
  have hv := canonical_return_coefficient_mem V L
  have all : ∀ z ∈ familyEndpointCosts P Q h U V W L, z ∈ coefficientField := by
    intro z hz
    simp only [familyEndpointCosts,List.mem_append] at hz
    rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz)
    · exact endpoint_costs_field _ _ P h hu.1 hu.2 z hz
    · exact endpoint_costs_field _ _ Q h hv.1 hv.2 z hz
    · exact endpoint_costs_field _ _ (U false) (W false) hu.1 hu.2 z hz
    · exact endpoint_costs_field _ _ (U true) (W true) hu.1 hu.2 z hz
    · exact endpoint_costs_field _ _ (V false) (W false) hv.1 hv.2 z hz
    · exact endpoint_costs_field _ _ (V true) (W true) hv.1 hv.2 z hz
  have fold : ∀ xs : List ℝ, (∀ z ∈ xs, z ∈ coefficientField) → xs.foldr max 0 ∈ coefficientField := by
    intro xs
    induction xs with
    | nil => intro _; exact coefficientField.zero_mem
    | cons z xs ih =>
      intro hxs
      exact endpoint_field_max _ _ (hxs z (by simp))
        (ih (fun y hy => hxs y (by simp [hy])))
  exact fold _ all

/-- Every feasible pair of fixed actual tails has budget at least the complete
indexed endpoint maximum. Their scalars need not lie in either canonical hull.
The same finite maximum belongs to the original field Q(t). -/
theorem original_fixed_tail_endpoint_budget
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (_hP : LegalWord .G0 s1 P) (_hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L)
    (hUlen : ∀ i, (U i).length = L) (hVlen : ∀ i, (V i).length = L)
    (hWlen : ∀ i, (W i).length = L)
    (hU : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (ξ η : ℕ → Label) (x y : ℕ → ℝ) (path1 path2 : ℕ → Guard)
    (_hpath1 : path1 0 = s1) (_hpath2 : path2 0 = s2)
    (b : ℝ) (hb : 0 ≤ b)
    (feasible : ∀ zs : List Bool,
      ClosedOriginalTailExtension b (P ++ choiceBlocks U zs) (h ++ choiceBlocks W zs) ξ x path1 ∧
      ClosedOriginalTailExtension b (Q ++ choiceBlocks V zs) (h ++ choiceBlocks W zs) η y path2) :
    familyEndpointBudget P Q h U V W L ≤ b ∧
      familyEndpointBudget P Q h U V W L ∈ coefficientField := by
  have hUW : ∀ i, (U i).length = (W i).length := fun i => (hUlen i).trans (hWlen i).symm
  have hVW : ∀ i, (V i).length = (W i).length := fun i => (hVlen i).trans (hWlen i).symm
  have high := endpoint_component_necessary b hb s1 P h hPlen U W L hL hUlen hWlen hU (x 0)
    (fun zs => endpoint_extension_slots b _ _
      (by simp only [List.length_append,hPlen,choice_lengths U W hUW zs])
      ξ x path1 (feasible zs).1)
  have low := endpoint_component_necessary b hb s2 Q h hQlen V W L hL hVlen hWlen hV (y 0)
    (fun zs => endpoint_extension_slots b _ _
      (by simp only [List.length_append,hQlen,choice_lengths V W hVW zs])
      η y path2 (feasible zs).2)
  have all : ∀ z ∈ familyEndpointCosts P Q h U V W L, z ≤ b := by
    intro z hz
    simp only [familyEndpointCosts,List.mem_append] at hz
    rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz)
    · exact endpoint_cost_le_of_certificate b _ _ P h high.1 z hz
    · exact endpoint_cost_le_of_certificate b _ _ Q h low.1 z hz
    · exact endpoint_cost_le_of_certificate b _ _ (U false) (W false) (high.2 false) z hz
    · exact endpoint_cost_le_of_certificate b _ _ (U true) (W true) (high.2 true) z hz
    · exact endpoint_cost_le_of_certificate b _ _ (V false) (W false) (low.2 false) z hz
    · exact endpoint_cost_le_of_certificate b _ _ (V true) (W true) (low.2 true) z hz
  have fold : ∀ xs : List ℝ, (∀ z ∈ xs, z ≤ b) → xs.foldr max 0 ≤ b := by
    intro xs
    induction xs with
    | nil => intro _; exact hb
    | cons z xs ih =>
      intro hxs
      exact max_le (hxs z (by simp)) (ih (fun q hq => hxs q (by simp [hq])))
  exact ⟨fold _ all,endpoint_family_budget_field P Q h U V W L⟩

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity
