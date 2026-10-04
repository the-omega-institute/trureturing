/- GID: D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Paid positive-time queries retain a live prime-power parent phase. -/
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController

open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity observe)
open D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

abbrev PositiveTime := {k : ℕ // 0 < k}
abbrev Tree := PassiveProtocol PositiveTime (fun _ => ℕ)

def read (p e : ℕ) (q : PositiveTime) (v : ℕ × ℕ) : ℕ :=
  actualGcd (p ^ e) q.val v

/-- Test real children in order. Exhaustion selects the omitted representative,
without appending an answer for that representative. -/
def children (threshold rank phase : ℕ) (next : ℕ → Tree) : ℕ → ℕ → Tree
  | 0, j => next (phase + j * rank)
  | n + 1, j => .query ⟨phase + j * rank + 1, by omega⟩ (fun answer =>
      if threshold ∣ answer then next (phase + j * rank)
      else children threshold rank phase next n (j + 1))

/-- Every stagnant lift pays for the currently surviving representative. -/
noncomputable def continuation (p content : ℕ) : ℕ → ℕ → ℕ → Tree
  | 0, _, _ => .stop
  | fuel + 1, d, phase =>
      let next := continuation p content fuel (d + 1)
      if zeroRank (p ^ (d + 1)) = zeroRank (p ^ d) then
        .query ⟨phase + 1, by omega⟩ (fun answer =>
          if p ^ (content + d + 1) ∣ answer then next phase else .stop)
      else children (p ^ (content + d + 1)) (zeroRank (p ^ d)) phase next (p - 1) 0

/-- The first-layer scan is paid, including times already used for content. -/
def firstLayer (threshold : ℕ) (next : ℕ → Tree) : ℕ → ℕ → Tree
  | 0, _ => .stop
  | n + 1, phase => .query ⟨phase + 1, by omega⟩ (fun answer =>
      if threshold ∣ answer then next phase
      else firstLayer threshold next n (phase + 1))

/-- The tree's choice of content depth depends only on its two paid answers.
Malformed answer pairs stop after those answers. -/
noncomputable def protocol (p e : ℕ) : Tree :=
  .query ⟨1, by omega⟩ (fun first => .query ⟨2, by omega⟩ (fun second =>
    let content := Nat.gcd first second
    if content = p ^ e then .stop
    else if h : ∃ c, c < e ∧ content = p ^ c then
      let c := Classical.choose h
      firstLayer (p ^ (c + 1)) (continuation p c (e - c - 1) 1) (zeroRank p) 0
    else .stop))

private def Hit (p e content d phase : ℕ) (v : ℕ × ℕ) : Prop :=
  p ^ (content + d) ∣ read p e ⟨phase + 1, by omega⟩ v

private def Agreement (p e content d : ℕ) (v w : ℕ × ℕ) : Prop :=
  ∀ j, j ≤ d → ∀ phase, Hit p e content j phase v ↔ Hit p e content j phase w

private theorem continuation_fiber (p e content : ℕ) (hp : p.Prime)
    (good : (ℕ × ℕ) → Prop)
    (phaseLaw : ∀ v, good v → ∀ d, 1 ≤ d → content + d ≤ e → ∀ t,
      Hit p e content d t v → ∀ k,
      (Hit p e content d k v ↔ k % zeroRank (p ^ d) = t % zeroRank (p ^ d)))
    (growthLaw : ∀ v, good v → ∀ d, 1 ≤ d → content + d + 1 ≤ e → ∀ t,
      zeroRank (p ^ (d + 1)) ≠ zeroRank (p ^ d) →
      Hit p e content d t v →
      (Hit p e content (d + 1) (t + (p - 1) * zeroRank (p ^ d)) v ↔
        ∀ j, j < p - 1 → ¬ Hit p e content (d + 1) (t + j * zeroRank (p ^ d)) v)) :
    ∀ fuel d t, 1 ≤ d → content + d + fuel ≤ e →
      (∀ v, (runPassiveProtocol (read p e) (continuation p content fuel d t) v).length
        ≤ fuel * (p - 1)) ∧
      (∀ v w, good v → good w → Hit p e content d t v → Hit p e content d t w →
        Agreement p e content d v w →
        runPassiveProtocol (read p e) (continuation p content fuel d t) v =
          runPassiveProtocol (read p e) (continuation p content fuel d t) w →
        Agreement p e content (d + fuel) v w) := by
  classical
  have pLarge := hp.two_le
  have lower (d k : ℕ) (v : ℕ × ℕ) :
      Hit p e content (d + 1) k v → Hit p e content d k v := by
    exact fun h => dvd_trans (pow_dvd_pow p (by omega)) h
  have extend (d t : ℕ) (hd : 1 ≤ d) (hde : content + d + 1 ≤ e)
      (v w : ℕ × ℕ) (hv : good v) (hw : good w)
      (hvhit : Hit p e content (d + 1) t v) (hwhit : Hit p e content (d + 1) t w)
      (agree : Agreement p e content d v w) : Agreement p e content (d + 1) v w := by
    intro j hj k
    by_cases same : j = d + 1
    · subst j
      rw [phaseLaw v hv (d + 1) (by omega) (by omega) t hvhit,
        phaseLaw w hw (d + 1) (by omega) (by omega) t hwhit]
    · exact agree j (by omega) k
  have childrenLength (threshold rank phase : ℕ) (next : ℕ → Tree) (bound : ℕ)
      (hnext : ∀ t v, (runPassiveProtocol (read p e) (next t) v).length ≤ bound) :
      ∀ n j v, (runPassiveProtocol (read p e) (children threshold rank phase next n j) v).length
        ≤ n + bound := by
    intro n
    induction n with
    | zero => intro j v; simpa [children] using hnext (phase + j * rank) v
    | succ n ih =>
      intro j v
      simp only [children, runPassiveProtocol, List.length_cons]
      split
      · have h := hnext (phase + j * rank) v; omega
      · have h := ih (j + 1) v; omega
  intro fuel
  induction fuel with
  | zero =>
    intro d t hd hde
    exact ⟨by intro v; simp [continuation, runPassiveProtocol],
      by intro v w hv hw hvt hwt agree same; simpa using agree⟩
  | succ fuel ih =>
    intro d t hd hde
    have next (t : ℕ) := ih (d + 1) t (by omega) (by omega)
    by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
    · constructor
      · intro v
        simp only [continuation, stagnant, ite_true, runPassiveProtocol, List.length_cons]
        split
        · have h := (next t).1 v
          rw [Nat.succ_mul]
          omega
        · simp only [runPassiveProtocol, List.length_nil]
          rw [Nat.succ_mul]
          omega
      · intro v w hv hw hvt hwt agree same
        simp only [continuation, stagnant, ite_true, runPassiveProtocol] at same
        have head := (List.cons.inj same).1
        have reply : read p e ⟨t + 1, by omega⟩ v = read p e ⟨t + 1, by omega⟩ w :=
          congrArg (fun z : Sigma (fun _ : PositiveTime => ℕ) => z.2) head
        have tails := (List.cons.inj same).2
        by_cases hit : Hit p e content (d + 1) t v
        · have hitw : Hit p e content (d + 1) t w := by
            simpa only [Hit, reply] using hit
          have hitRaw : p ^ (content + d + 1) ∣ read p e ⟨t + 1, by omega⟩ v := hit
          have hitwRaw : p ^ (content + d + 1) ∣ read p e ⟨t + 1, by omega⟩ w := hitw
          simp only [hitRaw, hitwRaw, ite_true] at tails
          have h := (next t).2 v w hv hw hit
            hitw
            (extend d t hd (by omega) v w hv hw
              hit
              hitw agree) tails
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        · have missw : ¬ Hit p e content (d + 1) t w := by
            simpa only [Hit, reply] using hit
          have extinct (v : ℕ × ℕ) (hv : good v) (parent : Hit p e content d t v)
              (miss : ¬ Hit p e content (d + 1) t v) :
              ∀ k, ¬ Hit p e content (d + 1) k v := by
            intro k hk
            have phase := (phaseLaw v hv d hd (by omega) t parent k).mp (lower d k v hk)
            apply miss
            apply (phaseLaw v hv (d + 1) (by omega) (by omega) k hk t).mpr
            simpa only [stagnant] using phase.symm
          intro j hj k
          by_cases low : j ≤ d
          · exact agree j low k
          · apply iff_of_false
            · intro h
              exact extinct v hv hvt hit k (dvd_trans (pow_dvd_pow p (by omega)) h)
            · intro h
              exact extinct w hw hwt missw k (dvd_trans (pow_dvd_pow p (by omega)) h)
    · constructor
      · intro v
        simp only [continuation, stagnant, ite_false]
        have h := childrenLength (p ^ (content + d + 1)) (zeroRank (p ^ d)) t
          (continuation p content fuel (d + 1)) (fuel * (p - 1))
          (fun t v => (next t).1 v) (p - 1) 0 v
        rw [Nat.succ_mul]
        omega
      · intro v w hv hw hvt hwt agree same
        simp only [continuation, stagnant, ite_false] at same
        have scan : ∀ n j, n + j = p - 1 →
            (∀ i, i < j → ¬ Hit p e content (d + 1) (t + i * zeroRank (p ^ d)) v) →
            (∀ i, i < j → ¬ Hit p e content (d + 1) (t + i * zeroRank (p ^ d)) w) →
            runPassiveProtocol (read p e)
              (children (p ^ (content + d + 1)) (zeroRank (p ^ d)) t
                (continuation p content fuel (d + 1)) n j) v =
            runPassiveProtocol (read p e)
              (children (p ^ (content + d + 1)) (zeroRank (p ^ d)) t
                (continuation p content fuel (d + 1)) n j) w →
            Agreement p e content (d + 1 + fuel) v w := by
          intro n
          induction n with
          | zero =>
            intro j hj av aw same
            have jlast : j = p - 1 := by omega
            subst j
            have hitv := (growthLaw v hv d hd (by omega) t stagnant hvt).mpr av
            have hitw := (growthLaw w hw d hd (by omega) t stagnant hwt).mpr aw
            exact (next (t + (p - 1) * zeroRank (p ^ d))).2 v w hv hw hitv hitw
              (extend d _ hd (by omega) v w hv hw hitv hitw agree)
              (by simpa [children] using same)
          | succ n ihscan =>
            intro j hj av aw same
            simp only [children, runPassiveProtocol] at same
            have reply : read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ v =
                read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ w :=
              congrArg (fun z : Sigma (fun _ : PositiveTime => ℕ) => z.2) (List.cons.inj same).1
            have tails := (List.cons.inj same).2
            by_cases hit : Hit p e content (d + 1) (t + j * zeroRank (p ^ d)) v
            · have hitw : Hit p e content (d + 1) (t + j * zeroRank (p ^ d)) w := by
                simpa only [Hit, reply] using hit
              apply (next (t + j * zeroRank (p ^ d))).2 v w hv hw hit hitw
                (extend d _ hd (by omega) v w hv hw hit hitw agree)
              have hitRaw : p ^ (content + d + 1) ∣ read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ v := hit
              have hitwRaw : p ^ (content + d + 1) ∣ read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ w := hitw
              simpa only [hitRaw, hitwRaw, ite_true] using tails
            · have missw : ¬ Hit p e content (d + 1) (t + j * zeroRank (p ^ d)) w := by
                simpa only [Hit, reply] using hit
              apply ihscan (j + 1) (by omega)
              · intro i hi
                by_cases old : i < j
                · exact av i old
                · have ij : i = j := by omega
                  simpa only [ij] using hit
              · intro i hi
                by_cases old : i < j
                · exact aw i old
                · have ij : i = j := by omega
                  simpa only [ij] using missw
              · have hitRaw : ¬ p ^ (content + d + 1) ∣ read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ v := hit
                have misswRaw : ¬ p ^ (content + d + 1) ∣ read p e ⟨t + j * zeroRank (p ^ d) + 1, by omega⟩ w := missw
                simpa only [hitRaw, misswRaw, ite_false] using tails
        have h := scan (p - 1) 0 (by omega) (by intro i hi; omega) (by intro i hi; omega) same
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem paid_first_layer (p e content : ℕ) (hp : p.Prime) (hc : content < e)
    (good : (ℕ × ℕ) → Prop)
    (base : ∀ v, good v → ∀ t, Hit p e content 0 t v)
    (phaseLaw : ∀ v, good v → ∀ d, 1 ≤ d → content + d ≤ e → ∀ t,
      Hit p e content d t v → ∀ k,
      (Hit p e content d k v ↔ k % zeroRank (p ^ d) = t % zeroRank (p ^ d)))
    (growthLaw : ∀ v, good v → ∀ d, 1 ≤ d → content + d + 1 ≤ e → ∀ t,
      zeroRank (p ^ (d + 1)) ≠ zeroRank (p ^ d) → Hit p e content d t v →
      (Hit p e content (d + 1) (t + (p - 1) * zeroRank (p ^ d)) v ↔
        ∀ j, j < p - 1 → ¬ Hit p e content (d + 1) (t + j * zeroRank (p ^ d)) v)) :
    let T := firstLayer (p ^ (content + 1))
      (continuation p content (e - content - 1) 1) (zeroRank p) 0
    (∀ v, (runPassiveProtocol (read p e) T v).length ≤
      zeroRank p + (e - content - 1) * (p - 1)) ∧
    (∀ v w, good v → good w → runPassiveProtocol (read p e) T v =
      runPassiveProtocol (read p e) T w → Agreement p e content (e - content) v w) := by
  classical
  have rankpos := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 1
  simp only [pow_one] at rankpos
  let fuel := e - content - 1
  let next := continuation p content fuel 1
  have nextSpec (t : ℕ) := continuation_fiber p e content hp good phaseLaw growthLaw
    fuel 1 t (by omega) (by dsimp [fuel]; omega)
  have hitAgreement (t : ℕ) (v w : ℕ × ℕ) (hv : good v) (hw : good w)
      (av : Hit p e content 1 t v) (aw : Hit p e content 1 t w) :
      Agreement p e content 1 v w := by
    intro j hj k
    by_cases zero : j = 0
    · subst j; exact iff_of_true (base v hv k) (base w hw k)
    · have one : j = 1 := by omega
      subst j
      rw [phaseLaw v hv 1 (by omega) (by omega) t av,
        phaseLaw w hw 1 (by omega) (by omega) t aw]
  have scan : ∀ n t, n + t = zeroRank p →
      (∀ v, (runPassiveProtocol (read p e) (firstLayer (p ^ (content + 1)) next n t) v).length
        ≤ n + fuel * (p - 1)) ∧
      (∀ v w, good v → good w →
        (∀ i, i < t → ¬ Hit p e content 1 i v) →
        (∀ i, i < t → ¬ Hit p e content 1 i w) →
        runPassiveProtocol (read p e) (firstLayer (p ^ (content + 1)) next n t) v =
          runPassiveProtocol (read p e) (firstLayer (p ^ (content + 1)) next n t) w →
        Agreement p e content (e - content) v w) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      constructor
      · intro v; simp [firstLayer, runPassiveProtocol]
      · intro v w hv hw av aw same
        have extinct (v : ℕ × ℕ) (hv : good v)
            (misses : ∀ i, i < t → ¬ Hit p e content 1 i v) :
            ∀ k, ¬ Hit p e content 1 k v := by
          intro k hit
          let r := k % zeroRank p
          have hr : r < t := by dsimp [r]; have h := Nat.mod_lt k rankpos.1; omega
          apply misses r hr
          apply (phaseLaw v hv 1 (by omega) (by omega) k hit r).mpr
          simp [r]
        intro j hj k
        by_cases zero : j = 0
        · subst j; exact iff_of_true (base v hv k) (base w hw k)
        · apply iff_of_false
          · intro hit
            exact extinct v hv av k (dvd_trans (pow_dvd_pow p (by omega)) hit)
          · intro hit
            exact extinct w hw aw k (dvd_trans (pow_dvd_pow p (by omega)) hit)
    | succ n ih =>
      intro t ht
      have later := ih (t + 1) (by omega)
      constructor
      · intro v
        simp only [firstLayer, runPassiveProtocol, List.length_cons]
        split
        · have h := (nextSpec t).1 v; dsimp [next] at *; omega
        · have h := later.1 v; omega
      · intro v w hv hw av aw same
        simp only [firstLayer, runPassiveProtocol] at same
        have reply : read p e ⟨t + 1, by omega⟩ v = read p e ⟨t + 1, by omega⟩ w :=
          congrArg (fun z : Sigma (fun _ : PositiveTime => ℕ) => z.2) (List.cons.inj same).1
        have tails := (List.cons.inj same).2
        by_cases hit : Hit p e content 1 t v
        · have hitw : Hit p e content 1 t w := by simpa only [Hit, reply] using hit
          have hitRaw : p ^ (content + 1) ∣ read p e ⟨t + 1, by omega⟩ v := hit
          have hitwRaw : p ^ (content + 1) ∣ read p e ⟨t + 1, by omega⟩ w := hitw
          simp only [hitRaw, hitwRaw, ite_true] at tails
          have h := (nextSpec t).2 v w hv hw hit hitw (hitAgreement t v w hv hw hit hitw) tails
          simpa [fuel, Nat.add_sub_of_le (by omega : content + 1 ≤ e),
            show 1 + (e - content - 1) = e - content by omega] using h
        · have missw : ¬ Hit p e content 1 t w := by simpa only [Hit, reply] using hit
          have hitRaw : ¬ p ^ (content + 1) ∣ read p e ⟨t + 1, by omega⟩ v := hit
          have misswRaw : ¬ p ^ (content + 1) ∣ read p e ⟨t + 1, by omega⟩ w := missw
          simp only [hitRaw, misswRaw, ite_false] at tails
          apply later.2 v w hv hw _ _ tails
          · intro i hi
            by_cases old : i < t
            · exact av i old
            · have it : i = t := by omega
              simpa only [it] using hit
          · intro i hi
            by_cases old : i < t
            · exact aw i old
            · have it : i = t := by omega
              simpa only [it] using missw
  have h := scan (zeroRank p) 0 (by omega)
  exact ⟨h.1, fun v w hv hw same => h.2 v w hv hw
    (by intro i hi; omega) (by intro i hi; omega) same⟩

theorem result (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ∃ T : Tree,
      (∀ v : ℕ × ℕ, (runPassiveProtocol (read p e) T v).length ≤
        zeroRank p + (e - 1) * (p - 1) + 2) ∧
      (∀ v w : ℕ × ℕ, runPassiveProtocol (read p e) T v =
        runPassiveProtocol (read p e) T w → ∀ k : ℕ, 0 < k →
          actualGcd (p ^ e) k v = actualGcd (p ^ e) k w) := by
  classical
  have contentLaw (v : ℕ × ℕ) :
      Nat.gcd (read p e ⟨1, by omega⟩ v) (read p e ⟨2, by omega⟩ v) =
        Nat.gcd (Nat.gcd v.1 v.2) (p ^ e) := by
    have law := (GraftAffineClosure.result.2 (p ^ e) (pow_pos hp.pos e) (step v)).2.2.2.2.1
    change Nat.gcd (Nat.gcd (quantity (step v)) (quantity (step (step v)))) (p ^ e) =
      Nat.gcd (Nat.gcd (step v).1 (step v).2) (p ^ e) at law
    have combine (a b m : ℕ) : Nat.gcd (Nat.gcd a m) (Nat.gcd b m) = Nat.gcd (Nat.gcd a b) m := by
      rw [Nat.gcd_assoc, ← Nat.gcd_assoc m b m, Nat.gcd_comm m b,
        Nat.gcd_assoc b m m, Nat.gcd_self, ← Nat.gcd_assoc]
    change Nat.gcd (Nat.gcd (quantity (step v)) (p ^ e))
      (Nat.gcd (quantity (step (step v))) (p ^ e)) = Nat.gcd (Nat.gcd v.1 v.2) (p ^ e)
    rw [combine]
    simpa only [step, Prod.fst, Prod.snd, Nat.gcd_add_self_right, Nat.gcd_comm v.2 v.1] using law
  let C (v : ℕ × ℕ) := Nat.gcd (Nat.gcd v.1 v.2) (p ^ e)
  have normalization (c : ℕ) (hc : c < e) (v : ℕ × ℕ) (hv : C v = p ^ c) :
      ∃ u : ℕ × ℕ, v = (p ^ c * u.1, p ^ c * u.2) ∧
        Primitive p (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ)) := by
    have Qdiv : p ^ c ∣ Nat.gcd v.1 v.2 := by
      rw [← hv]; exact Nat.gcd_dvd_left _ _
    obtain ⟨a, ha⟩ := dvd_trans Qdiv (Nat.gcd_dvd_left v.1 v.2)
    obtain ⟨b, hb⟩ := dvd_trans Qdiv (Nat.gcd_dvd_right v.1 v.2)
    let u : ℕ × ℕ := (a, b)
    have equal : v = (p ^ c * u.1, p ^ c * u.2) := Prod.ext ha hb
    refine ⟨u, equal, ?_⟩
    by_contra h
    have coords : p ∣ (GraftAffineClosure.observe u).1 ∧ p ∣ (GraftAffineClosure.observe u).2 := by
      simpa only [Primitive, not_or, not_not, Int.natCast_dvd_natCast] using h
    have cap := (GraftAffineClosure.result.2 p hp.pos u).2.2.2.2.1
    have obsDiv : p ∣ Nat.gcd (Nat.gcd (GraftAffineClosure.quantity u)
        (GraftAffineClosure.quantity (GraftAffineClosure.step u))) p :=
      Nat.dvd_gcd (Nat.dvd_gcd coords.1 coords.2) (dvd_refl _)
    rw [cap] at obsDiv
    have udiv := dvd_trans obsDiv (Nat.gcd_dvd_left (Nat.gcd u.1 u.2) p)
    have full : p ^ (c + 1) ∣ C v := by
      apply Nat.dvd_gcd _ (pow_dvd_pow p (by omega))
      rw [equal, Nat.gcd_mul_left, pow_succ]
      exact Nat.mul_dvd_mul_left (p ^ c) udiv
    rw [hv] at full
    have bad := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp full
    omega
  have fiberLaws (c : ℕ) (hc : c < e) :
      (∀ v, C v = p ^ c → ∀ t, Hit p e c 0 t v) ∧
      (∀ v, C v = p ^ c → ∀ d, 1 ≤ d → c + d ≤ e → ∀ t,
        Hit p e c d t v → ∀ k,
        (Hit p e c d k v ↔ k % zeroRank (p ^ d) = t % zeroRank (p ^ d))) ∧
      (∀ v, C v = p ^ c → ∀ d, 1 ≤ d → c + d + 1 ≤ e → ∀ t,
        zeroRank (p ^ (d + 1)) ≠ zeroRank (p ^ d) → Hit p e c d t v →
        (Hit p e c (d + 1) (t + (p - 1) * zeroRank (p ^ d)) v ↔
          ∀ j, j < p - 1 → ¬ Hit p e c (d + 1) (t + j * zeroRank (p ^ d)) v)) := by
    have hitTransport (v u : ℕ × ℕ) (equal : v = (p ^ c * u.1, p ^ c * u.2))
        (d t : ℕ) (hd : c + d ≤ e) :
        Hit p e c d t v ↔ (p : ℤ) ^ d ∣
          signedValue (t + 1) (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ)) := by
      rw [Hit, read, actualGcd, Nat.dvd_gcd_iff, and_iff_left (pow_dvd_pow p hd),
        equal, actual_quantity_scaling, pow_add,
        Nat.mul_dvd_mul_iff_left (pow_pos hp.pos c)]
      rw [← actual_signed_quantity (t + 1) u (by omega), ← Nat.cast_pow,
        Int.natCast_dvd_natCast]
    have signed (x : ℤ × ℤ) (k : ℕ) (hk : 0 < k) :
        PrimePowerGcdHorizon.signedObservation x.1 x.2 k = signedValue k x := by
      simp only [PrimePowerGcdHorizon.signedObservation, signedValue,
        show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, Int.fib_natCast]
    have primitivePhase (u : ℕ × ℕ)
        (primitive : Primitive p (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ)))
        (d : ℕ) (hd : 1 ≤ d) (t : ℕ)
        (hit : (p : ℤ) ^ d ∣ signedValue (t + 1)
          (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ))) :
        ∀ k, ((p : ℤ) ^ d ∣ signedValue (k + 1)
          (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ)) ↔
          k % zeroRank (p ^ d) = t % zeroRank (p ^ d)) := by
      let x : ℤ × ℤ := (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ))
      have nhit : (p : ℤ) ∣ PrimePowerGcdHorizon.signedObservation x.1 x.2 (t + 1) := by
        rw [signed x (t + 1) (by omega)]
        exact dvd_trans (dvd_pow_self (p : ℤ) (by omega)) hit
      have previous : ¬ (p : ℤ) ∣ PrimePowerGcdHorizon.signedObservation x.1 x.2 t := by
        intro prev
        have bad := (PrimePowerGcdHorizon.adjacent_divisibility p hp x.1 x.2 t).mp ⟨prev, nhit⟩
        exact primitive.elim (fun h => h bad.1) (fun h => h bad.2)
      let a := (GraftAffineClosure.step^[t] (GraftAffineClosure.observe u)).1
      have first : (a : ℤ) = PrimePowerGcdHorizon.signedObservation x.1 x.2 t := by
        by_cases zero : t = 0
        · simp [a, x, zero, PrimePowerGcdHorizon.signedObservation]
        · rw [signed x t (by omega)]
          simp [a, iterate_first t (by omega), signedValue, x]
      have notdvd : ¬ p ∣ a := by
        intro h
        apply previous
        rw [← first]
        exact Int.natCast_dvd_natCast.mpr h
      have unit : IsUnit (a : ZMod (p ^ d)) :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr notdvd
      have statecast :
          ((GraftAffineClosure.step^[t] ((x.1, x.2) : ZMod (p ^ d) × ZMod (p ^ d))).1) =
          (a : ZMod (p ^ d)) := by
        by_cases zero : t = 0
        · simp [zero, a, x]
        · simp [iterate_first t (by omega), a, x, Nat.cast_add, Nat.cast_mul]
      intro k
      apply phase_from_unit p hp d hd t k x
      · rw [statecast]; exact unit
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        simpa using hit
    refine ⟨?_, ?_, ?_⟩
    · intro v hv t
      obtain ⟨u, equal, _⟩ := normalization c hc v hv
      rw [hitTransport v u equal 0 t (by omega)]
      simp
    · intro v hv d hd hde t hit k
      obtain ⟨u, equal, primitive⟩ := normalization c hc v hv
      rw [hitTransport v u equal d k hde]
      exact primitivePhase u primitive d hd t ((hitTransport v u equal d t hde).mp hit) k
    · intro v hv d hd hde t growing hit
      obtain ⟨u, equal, primitive⟩ := normalization c hc v hv
      let x : ℤ × ℤ := (((GraftAffineClosure.observe u).1 : ℤ), ((GraftAffineClosure.observe u).2 : ℤ))
      have dichotomy := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p (d + 1) hp (by omega)).2.1
      have growth : zeroRank (p ^ (d + 1)) = p * zeroRank (p ^ d) := by
        simpa only [Nat.add_sub_cancel] using dichotomy.resolve_left (by simpa using growing)
      have dec := PrimePowerGcdHorizon.parent_hit_decoder p (d + 1) hp (by omega) growth x.1 x.2
        (by simpa only [Primitive, not_and_or] using primitive) (t + 1)
        (by rw [signed x (t + 1) (by omega)]; simpa only [Nat.add_sub_cancel, Nat.cast_pow] using
          (hitTransport v u equal d t (by omega)).mp hit)
      have shifted (j : ℕ) :
          PrimePowerGcdHorizon.signedObservation x.1 x.2
            (t + 1 + j * zeroRank (p ^ d)) =
          signedValue (t + j * zeroRank (p ^ d) + 1) x := by
        rw [show t + 1 + j * zeroRank (p ^ d) = t + j * zeroRank (p ^ d) + 1 by omega]
        exact signed x _ (by omega)
      simp only [Nat.add_sub_cancel, shifted, Nat.cast_pow] at dec
      constructor
      · intro last j hj child
        apply dec.mp ((hitTransport v u equal (d + 1) _ (by omega)).mp last) j hj
        exact (hitTransport v u equal (d + 1) _ (by omega)).mp child
      · intro misses
        apply (hitTransport v u equal (d + 1) _ (by omega)).mpr
        apply dec.mpr
        intro j hj child
        exact misses j hj ((hitTransport v u equal (d + 1) _ (by omega)).mpr child)
  have future (c : ℕ) (hc : c < e) (v w : ℕ × ℕ)
      (hv : C v = p ^ c) (hw : C w = p ^ c)
      (agree : Agreement p e c (e - c) v w) :
      ∀ k, 0 < k → actualGcd (p ^ e) k v = actualGcd (p ^ e) k w := by
    intro k hk
    apply Nat.gcd_left_eq_iff.mpr
    intro divisor divides
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp divides
    by_cases low : j ≤ c
    · have bv := (fiberLaws c hc).1 v hv (k - 1)
      have bw := (fiberLaws c hc).1 w hw (k - 1)
      have vdiv := dvd_trans (pow_dvd_pow p low) (dvd_trans bv (Nat.gcd_dvd_left _ _))
      have wdiv := dvd_trans (pow_dvd_pow p low) (dvd_trans bw (Nat.gcd_dvd_left _ _))
      simpa only [Hit, read, actualGcd, Nat.sub_add_cancel hk, Nat.add_zero] using iff_of_true vdiv wdiv
    · have h := agree (j - c) (by omega) (k - 1)
      simpa only [Hit, read, actualGcd, show c + (j - c) = j by omega,
        Nat.sub_add_cancel hk, Nat.dvd_gcd_iff, and_iff_left (pow_dvd_pow p hj)] using h
  have saturated (v : ℕ × ℕ) (hv : C v = p ^ e) (k : ℕ) : actualGcd (p ^ e) k v = p ^ e := by
    have dv : p ^ e ∣ Nat.gcd v.1 v.2 := by rw [← hv]; exact Nat.gcd_dvd_left _ _
    apply Nat.gcd_eq_right
    rw [actual_source_value]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_trans dv (Nat.gcd_dvd_left _ _)) _)
      (dvd_mul_of_dvd_right (dvd_trans dv (Nat.gcd_dvd_right _ _)) _)
  refine ⟨protocol p e, ?_, ?_⟩
  · intro v
    simp only [protocol, runPassiveProtocol, List.length_cons]
    split
    · simp only [runPassiveProtocol, List.length_nil]; omega
    · split
      · rename_i h
        have spec := Classical.choose_spec h
        have f := paid_first_layer p e (Classical.choose h) hp spec.1
          (fun v => C v = p ^ Classical.choose h) (fiberLaws _ spec.1).1
          (fiberLaws _ spec.1).2.1 (fiberLaws _ spec.1).2.2
        have bound := f.1 v
        have budget := Nat.mul_le_mul_right (p - 1)
          (show e - Classical.choose h - 1 ≤ e - 1 by omega)
        omega
      · simp only [runPassiveProtocol, List.length_nil]; omega
  · intro v w same k hk
    simp only [protocol, runPassiveProtocol] at same
    have first : read p e ⟨1, by omega⟩ v = read p e ⟨1, by omega⟩ w :=
      congrArg (fun z : Sigma (fun _ : PositiveTime => ℕ) => z.2) (List.cons.inj same).1
    have tails := (List.cons.inj same).2
    have second : read p e ⟨2, by omega⟩ v = read p e ⟨2, by omega⟩ w :=
      congrArg (fun z : Sigma (fun _ : PositiveTime => ℕ) => z.2) (List.cons.inj tails).1
    have history := (List.cons.inj tails).2
    have sameContent : C v = C w := by
      change Nat.gcd (Nat.gcd v.1 v.2) (p ^ e) = Nat.gcd (Nat.gcd w.1 w.2) (p ^ e)
      rw [← contentLaw v, ← contentLaw w, first, second]
    rw [first, second] at history
    by_cases cap : Nat.gcd (read p e ⟨1, by omega⟩ w) (read p e ⟨2, by omega⟩ w) = p ^ e
    · have hw : C w = p ^ e := (contentLaw w).symm.trans cap
      rw [saturated v (sameContent.trans hw), saturated w hw]
    · have depth : ∃ c, c < e ∧
          Nat.gcd (read p e ⟨1, by omega⟩ w) (read p e ⟨2, by omega⟩ w) = p ^ c := by
        obtain ⟨c, hc, equal⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right (Nat.gcd w.1 w.2) (p ^ e))
        refine ⟨c, ?_, (contentLaw w).trans equal⟩
        have ne : c ≠ e := fun h => cap ((contentLaw w).trans (by simpa [h] using equal))
        omega
      simp only [cap, ite_false, dif_pos depth] at history
      have spec := Classical.choose_spec depth
      have hw : C w = p ^ Classical.choose depth := (contentLaw w).symm.trans spec.2
      have f := paid_first_layer p e (Classical.choose depth) hp spec.1
        (fun v => C v = p ^ Classical.choose depth) (fiberLaws _ spec.1).1
        (fiberLaws _ spec.1).2.1 (fiberLaws _ spec.1).2.2
      exact future _ spec.1 v w (sameContent.trans hw) hw
        (f.2 v w (sameContent.trans hw) hw history) k hk

#print axioms result

end D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController
