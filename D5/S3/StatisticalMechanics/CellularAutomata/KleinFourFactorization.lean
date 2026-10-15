/- GID: D5/S3/StatisticalMechanics/CellularAutomata/KleinFourFactorization
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/KleinFourFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive membership and actual-configuration transport for binary Klein four. -/

/-
MIT License

Copyright (c) 2026 Edgar Alcalá-Arroyo, Alonso Castillo-Ramirez, Haobo Ma, Wenlin Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Public source: https://github.com/the-omega-institute/klein-four-lazy-ca-supplement
Version v1.1.0, commit fae47ad9dbbd4cbc1462a058dffe6ad4c2e416f1.
DOI: 10.5281/zenodo.23280244. Adapted structural proof; fixed counts excluded.
-/

import D5.S3.StatisticalMechanics.CellularAutomata.KleinFourInvariant
import D5.S3.StatisticalMechanics.CellularAutomata.LazyInvertibleGeneration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization

open D5.S3.StatisticalMechanics.CellularAutomata.KleinFourInvariant

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def unit (cflip : Bool) (pflip : Fin 3 → Bool) (swap : Bool) (offset : Bool → G) : CA :=
  ({ lower := { c := fun b => xor b cflip, p := fun s => (true, pflip s) },
     free := fun b => .f (xor b swap) (offset b) } : Table).ca

def unitInv (cflip : Bool) (pflip : Fin 3 → Bool) (swap : Bool) (offset : Bool → G) : CA :=
  unit cflip pflip swap (fun b => offset (xor b swap))

theorem unit_left (c p s o) : unitInv c p s o * unit c p s o = 1 := by
  ext x
  cases x with
  | c b => exact (by decide : ∀ c b : Bool, X.c (xor (xor b c) c) = X.c b) c b
  | p t b => exact (by decide : ∀ (t : Fin 3) (a b : Bool), X.p t (xor a (xor a b)) = X.p t b) t (p t) b
  | f b g =>
    change X.f (xor (xor b s) s) (gm (o (xor (xor b s) s)) (gm (o b) g)) = X.f b g
    exact (by decide : ∀ s (o : Bool → G) b g,
      X.f (xor (xor b s) s) (gm (o (xor (xor b s) s)) (gm (o b) g)) = X.f b g) s o b g

theorem unit_right (c p s o) : unit c p s o * unitInv c p s o = 1 := by
  ext x
  cases x with
  | c b => exact (by decide : ∀ c b : Bool, X.c (xor (xor b c) c) = X.c b) c b
  | p t b => exact (by decide : ∀ (t : Fin 3) (a b : Bool), X.p t (xor a (xor a b)) = X.p t b) t (p t) b
  | f b g =>
    change X.f (xor (xor b s) s) (gm (o (xor b s)) (gm (o (xor b s)) g)) = X.f b g
    exact (by decide : ∀ s (o : Bool → G) b g,
      X.f (xor (xor b s) s) (gm (o (xor b s)) (gm (o (xor b s)) g)) = X.f b g) s o b g

theorem unit_ICA (c p s o) : unit c p s o ∈ ICA := by
  constructor
  · intro x y h
    have h' := congrArg (unitInv c p s o) h
    change (unitInv c p s o * unit c p s o) x =
      (unitInv c p s o * unit c p s o) y at h'
    rw [unit_left] at h'
    change x = y at h'
    exact h'
  · intro y
    refine ⟨unitInv c p s o y, ?_⟩
    change (unit c p s o * unitInv c p s o) y = y
    rw [unit_right]
    rfl

theorem ICA_mem {T : CA} (h : T ∈ ICA) : T ∈ M := Submonoid.subset_closure (Or.inl h)
theorem lazy_mem (S : Finset G) (p : Bits) (h : e ∈ S) : lazyMap S p ∈ M :=
  Submonoid.subset_closure (Or.inr ⟨S, p, h, rfl⟩)
theorem fullLazy_mem (x : X) : lazyMap Finset.univ (encode x) ∈ M :=
  lazy_mem _ _ (Finset.mem_univ _)
theorem unit_mem (c p s o) : unit c p s o ∈ M := ICA_mem (unit_ICA c p s o)
theorem unitInv_mem (c p s o) : unitInv c p s o ∈ M := unit_mem _ _ _ _

def constantCollapse (b : Bool) : CA :=
  ({ lower := { c := fun _ => b, p := fun _ => (true, false) },
     free := fun j => .f j e } : Table).ca

def pairCollapse (s : Fin 3) (b : Bool) : CA :=
  ({ lower := { c := id, p := fun t => if t = s then (false, b) else (true, false) },
     free := fun j => .f j e } : Table).ca

def freeCollapse (j : Bool) (y : X) : CA :=
  ({ lower := { c := id, p := fun _ => (true, false) },
     free := fun k => if k = j then y else .f k e } : Table).ca

/-- Lemma 2.4: fixed-point and two-point collapses are full-neighborhood lazy. -/
theorem constantCollapse_lazy : ∀ b x,
    constantCollapse b x = lazyMap Finset.univ (encode (.c (!b))) x := by
  dsimp only [constantCollapse, Table.ca, lazyMap, ofRule]
  decide
theorem pairCollapse_lazy : ∀ s b x,
    pairCollapse s b x = lazyMap Finset.univ (encode (.p s (!b))) x := by
  dsimp only [pairCollapse, Table.ca, lazyMap, ofRule]
  decide

theorem constantCollapse_mem (b) : constantCollapse b ∈ M := by
  have h : constantCollapse b = lazyMap Finset.univ (encode (.c (!b))) := CA.ext (constantCollapse_lazy b)
  rw [h]; exact fullLazy_mem _

theorem pairCollapse_mem (s b) : pairCollapse s b ∈ M := by
  have h : pairCollapse s b = lazyMap Finset.univ (encode (.p s (!b))) := CA.ext (pairCollapse_lazy s b)
  rw [h]; exact fullLazy_mem _

def kernelCell (s : Fin 3) : G :=
  if s = 0 then (false, true) else if s = 1 then (true, false) else (true, true)

def freeToPairUnit (j : Bool) (s : Fin 3) (b : Bool) : CA :=
  unit false (fun t => if t = s then !b else false) j (fun _ => kernelCell s)

def freeToPairUnitInv (j : Bool) (s : Fin 3) (b : Bool) : CA :=
  unitInv false (fun t => if t = s then !b else false) j (fun _ => kernelCell s)

/-- Lemma 2.4's conjugation, checked only on the elementary collapses. -/
theorem freeToConstant_factor : ∀ j b x,
    freeCollapse j (.c b) x =
      (unit b (fun _ => false) j (fun _ => e) *
        lazyMap Finset.univ (encode (.f false e)) *
        unitInv b (fun _ => false) j (fun _ => e)) x := by
  simp only [mul_apply]
  dsimp only [freeCollapse, unit, unitInv, Table.ca, lazyMap, ofRule]
  decide

theorem freeToPair_factor : ∀ j s b x,
    freeCollapse j (.p s b) x =
      (freeToPairUnit j s b * lazyMap Finset.univ (encode (.f false (kernelCell s))) *
        freeToPairUnitInv j s b) x := by
  simp only [mul_apply]
  dsimp only [freeCollapse, freeToPairUnit, freeToPairUnitInv, unit, unitInv, Table.ca, lazyMap, ofRule]
  decide

theorem freeCollapse_mem (j : Bool) (y : X) (hy : freeOrbit y = none) : freeCollapse j y ∈ M := by
  cases y with
  | c b =>
    rw [CA.ext (freeToConstant_factor j b)]
    exact M.mul_mem (M.mul_mem (unit_mem _ _ _ _) (fullLazy_mem _)) (unitInv_mem _ _ _ _)
  | p s b =>
    rw [CA.ext (freeToPair_factor j s b)]
    exact M.mul_mem (M.mul_mem (unit_mem _ _ _ _) (fullLazy_mem _)) (unitInv_mem _ _ _ _)
  | f b g => simp [freeOrbit] at hy

def lowerMap (l : Lower) : CA :=
  ({ lower := l, free := fun j => .f j e } : Table).ca

def constantPart (c : Bool → Bool) : CA :=
  if c false = c true then constantCollapse (c false)
  else unit (c false) (fun _ => false) false (fun _ => e)

def pairPart (s : Fin 3) (d : Small) : CA :=
  if d.1 then unit false (fun t => if t = s then d.2 else false) false (fun _ => e)
  else pairCollapse s d.2

theorem constantPart_mem (c) : constantPart c ∈ M := by
  unfold constantPart
  split
  · exact constantCollapse_mem _
  · exact unit_mem _ _ _ _

theorem pairPart_mem (s d) : pairPart s d ∈ M := by
  unfold pairPart
  split
  · exact unit_mem _ _ _ _
  · exact pairCollapse_mem _ _

theorem lower_factor : ∀ l x,
    lowerMap l x = (pairPart 2 (l.p 2) * pairPart 1 (l.p 1) * pairPart 0 (l.p 0) *
      constantPart l.c) x := by
  simp only [mul_apply]
  dsimp only [lowerMap, pairPart, constantPart, pairCollapse, constantCollapse, unit, Table.ca]
  decide

/-- Proposition 2.5: the lower stratum is generated independently. -/
theorem lowerMap_mem (l) : lowerMap l ∈ M := by
  rw [CA.ext (lower_factor l)]
  exact M.mul_mem (M.mul_mem (M.mul_mem (pairPart_mem _ _) (pairPart_mem _ _))
    (pairPart_mem _ _)) (constantPart_mem _)

def freeOffset : X → G
  | .f _ g => g
  | _ => e

def normalizeSwap (f : Free) : Bool :=
  match freeOrbit (f false), freeOrbit (f true) with
  | some j, _ => j
  | none, some j => !j
  | none, none => false

def normalizer (f : Free) : CA :=
  unit false (fun _ => false) (normalizeSwap f) (fun b => freeOffset (f b))

def residual (f : Free) (b : Bool) : CA :=
  if freeOrbit (f b) = none then freeCollapse (xor b (normalizeSwap f)) (f b) else 1

def FreeMerges (f : Free) : Prop :=
  ∃ b, freeOrbit (f false) = some b ∧ freeOrbit (f true) = some b

instance (f : Free) : Decidable (FreeMerges f) := inferInstanceAs (Decidable (∃ b, _))

theorem residual_mem (f b) : residual f b ∈ M := by
  unfold residual
  split
  · exact freeCollapse_mem _ _ ‹_›
  · exact M.one_mem

theorem normalizer_lower : ∀ f x, freeOrbit x = none → normalizer f x = x := by
  dsimp only [normalizer, unit, Table.ca]
  decide
theorem residual_lower : ∀ f b x, freeOrbit x = none → residual f b x = x := by
  intro f b x hx
  unfold residual
  split
  · change (freeCollapse (xor b (normalizeSwap f)) (f b)) x = x
    exact (by
      dsimp only [freeCollapse, Table.ca]
      decide : ∀ j y x, freeOrbit x = none → freeCollapse j y x = x)
        _ _ x hx
  · rfl

theorem lowerMap_free (l : Lower) (b : Bool) (g : G) : lowerMap l (.f b g) = .f b g := by
  change act g (.f b e) = .f b g
  exact free_rep b g

theorem normalizer_free : ∀ f b g, ∃ j h, normalizer f (.f b g) = .f j h := by
  dsimp only [normalizer, unit, Table.ca]
  decide

/-- A partial permutation of the free strata extends to a unit. -/
theorem nonmerge_free_factor : ∀ f,
    ¬ FreeMerges f → ∀ b g,
    (residual f true * residual f false * normalizer f) (.f b g) = act g (f b) := by
  simp only [mul_apply]
  dsimp only [residual, normalizer, unit, freeCollapse, Table.ca]
  decide

theorem nonmerge_factor (t : Table) (h : ¬ Merges t.ca) :
    t.ca = residual t.free true * residual t.free false * lowerMap t.lower * normalizer t.free := by
  ext x
  cases x with
  | c b =>
    change X.c (t.lower.c b) = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.c b))))
    rw [normalizer_lower _ _ rfl]
    change X.c (t.lower.c b) = residual t.free true (residual t.free false (.c (t.lower.c b)))
    rw [residual_lower t.free false _ rfl, residual_lower t.free true _ rfl]
  | p s b =>
    change smallRun s (t.lower.p s) b = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.p s b))))
    rw [normalizer_lower _ _ rfl]
    change smallRun s (t.lower.p s) b = residual t.free true
      (residual t.free false (smallRun s (t.lower.p s) b))
    have hp : freeOrbit (smallRun s (t.lower.p s) b) = none :=
      (by decide : ∀ s d b, freeOrbit (smallRun s d b) = none) _ _ _
    rw [residual_lower _ _ _ hp, residual_lower _ _ _ hp]
  | f b g =>
    change act g (t.free b) = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.f b g))))
    obtain ⟨j, a, ha⟩ := normalizer_free t.free b g
    rw [ha, lowerMap_free, ← ha]
    have h' : ¬ FreeMerges t.free := by
      simpa only [Merges, FreeMerges, Table.ca, Table.run, act_e] using h
    exact (nonmerge_free_factor t.free h' b g).symm

theorem nonmerge_mem (T : CA) (h : ¬ Merges T) : T ∈ M := by
  have h' : ¬ Merges (tableOf T).ca := by rwa [ca_tableOf]
  rw [← ca_tableOf T, nonmerge_factor _ h']
  exact M.mul_mem (M.mul_mem (M.mul_mem (residual_mem _ _) (residual_mem _ _))
    (lowerMap_mem _)) (unit_mem _ _ _ _)

/-- Equation (3.1): B_s flips a central one whose s-neighbor is also one. -/
def B (s : Fin 3) : CA := lazyMap {e, kernelCell s} (fun _ => true)

theorem B_mem (s) : B s ∈ M := lazy_mem _ _ (by simp)

theorem B_lower : ∀ s x, freeOrbit x = none →
    B s x = match x with
      | .c _ => .c false
      | .p t b => if t = s then .c false else .p t b
      | _ => x := by
  dsimp only [B, lazyMap, ofRule]
  decide

theorem B_free : ∀ s b g, B s (.f b g) = .f false (gm (if b then kernelCell s else e) g) := by
  dsimp only [B, lazyMap, ofRule]
  decide

def mergeNormalizer (s : Fin 3) (f : Free) : CA :=
  unit false (fun _ => false) false
    (fun b => gm (if b then kernelCell s else e) (freeOffset (f b)))

theorem mergeNormalizer_free (s : Fin 3) (f : Free) (b : Bool) (g : G) :
    mergeNormalizer s f (.f b g) =
      .f b (gm (gm (if b then kernelCell s else e) (freeOffset (f b))) g) := by
  cases b <;> rfl

def mergeR (l : Lower) (q : Bool) : CA :=
  ({ lower := l, free := fun b => .f (xor b q) e } : Table).ca

theorem mergeR_first (l : Lower) (q : Bool) (g : G) :
    mergeR l q (.f false g) = act g (.f q e) := by
  cases q <;> rfl

theorem mergeR_not_merges : ∀ l q, ¬ Merges (mergeR l q) := by
  intro l q
  exact (by decide : ∀ q, ¬ FreeMerges (fun b => X.f (xor b q) e)) q

theorem merge_free_factor (l : Lower) : ∀ s f q,
    freeOrbit (f false) = some q → freeOrbit (f true) = some q → ∀ b g,
    act g (f b) = mergeR l q (B s (mergeNormalizer s f (.f b g))) := by
  intro s f q h0 h1 b g
  rw [mergeNormalizer_free, B_free, mergeR_first]
  exact (by decide : ∀ s f q,
    freeOrbit (f false) = some q → freeOrbit (f true) = some q → ∀ b g,
    act g (f b) = act
      (gm (if b then kernelCell s else e)
        (gm (gm (if b then kernelCell s else e) (freeOffset (f b))) g)) (.f q e))
      s f q h0 h1 b g

/-- Proposition 3.3: the three-factor construction for a merging member. -/
theorem merge_factor (t : Table) (s : Fin 3) (a q : Bool)
    (h0 : t.ca (.c false) = .c a) (h1 : t.ca (.c true) = .c a)
    (hp0 : t.ca (.p s false) = .c a) (hp1 : t.ca (.p s true) = .c a)
    (hf0 : freeOrbit (t.free false) = some q) (hf1 : freeOrbit (t.free true) = some q) :
    t.ca = mergeR t.lower q * B s * mergeNormalizer s t.free := by
  ext x
  cases x with
  | c b =>
    have hc : ∀ b, t.ca (.c b) = .c a := by intro b; cases b <;> assumption
    change t.ca (.c b) = mergeR t.lower q (B s (mergeNormalizer s t.free (.c b)))
    have hn : mergeNormalizer s t.free (.c b) = .c b := by
      change .c (xor b false) = X.c b
      cases b <;> rfl
    rw [hn, B_lower _ _ rfl]
    exact (hc b).trans (hc false).symm
  | p r b =>
    change t.ca (.p r b) = mergeR t.lower q (B s (mergeNormalizer s t.free (.p r b)))
    have hn : mergeNormalizer s t.free (.p r b) = .p r b := by
      change smallRun r (true, false) b = .p r b
      cases b <;> rfl
    rw [hn, B_lower _ _ rfl]
    by_cases hr : r = s
    · subst r
      simp only [if_pos rfl]
      have hp : t.ca (.p s b) = .c a := by cases b <;> assumption
      exact hp.trans h0.symm
    · simp only [if_neg hr]
      rfl
  | f b g => exact merge_free_factor t.lower s t.free q hf0 hf1 b g

theorem criterion_implies_membership (T : CA) (h : Criterion T) : T ∈ M := by
  by_cases hm : Merges T
  · obtain ⟨q, hf0, hf1⟩ := hm
    obtain ⟨s, a, h0, h1, hp0, hp1⟩ := h ⟨q, hf0, hf1⟩
    let t := tableOf T
    have ht : t.ca = T := ca_tableOf T
    have heq := merge_factor t s a q (ht.symm ▸ h0) (ht.symm ▸ h1)
      (ht.symm ▸ hp0) (ht.symm ▸ hp1) hf0 hf1
    rw [← ht, heq]
    exact M.mul_mem (M.mul_mem (nonmerge_mem _ (mergeR_not_merges _ _)) (B_mem _))
      (unit_mem _ _ _ _)
  · exact nonmerge_mem T hm


abbrev H := Multiplicative (ZMod 2 × ZMod 2)
abbrev Config := H → Bool

def phi : G ≃ H where
  toFun g := Multiplicative.ofAdd (if g.1 then 1 else 0, if g.2 then 1 else 0)
  invFun h := (decide (h.toAdd.1 = 1), decide (h.toAdd.2 = 1))
  left_inv := by decide
  right_inv := by decide

theorem phi_e : phi e = 1 := rfl
theorem phi_mul : ∀ g h, phi (gm g h) = phi g * phi h := by decide

def q : X ≃ Config where
  toFun x h := encode x (phi.symm h)
  invFun z := decode (fun g => z (phi g))
  left_inv x := by simp [decode_encode]
  right_inv z := by funext h; simp [encode_decode]

def rho (h : H) (x : Config) : Config := fun k => x (k * h)

theorem q_act (g : G) (x : X) : q (act g x) = rho (phi g) (q x) := by
  funext h
  obtain ⟨a, rfl⟩ := phi.surjective h
  simp only [q, Equiv.coe_fn_mk, rho, ← phi_mul, Equiv.symm_apply_apply, encode_act]

def lift : CA →* Function.End Config where
  toFun T x := q (T (q.symm x))
  map_one' := by funext x; exact q.apply_symm_apply x
  map_mul' A B := by
    funext x
    change q (A (B (q.symm x))) = q (A (q.symm (q (B (q.symm x)))))
    rw [q.symm_apply_apply]

theorem lift_apply (T : CA) (x : X) : lift T (q x) = q (T x) := by
  change q (T (q.symm (q x))) = _
  rw [q.symm_apply_apply]

theorem lift_injective : Function.Injective lift := by
  intro A B h
  apply CA.ext
  intro x
  apply q.injective
  simpa only [lift_apply] using congrFun h (q x)

theorem actual_equiv_iff (T : Function.End Config) :
    LazyInvertibleGeneration.IsCA T ↔ ∀ x h, T (rho h x) = rho h (T x) := by
  constructor
  · rintro ⟨S, μ, hT⟩ x h
    funext k
    change T (rho h x) k = T x (k * h)
    rw [hT, hT]
    simp only [rho, mul_assoc]
  · intro heq
    refine ⟨Finset.univ, fun z => T (fun h => z ⟨h, Finset.mem_univ h⟩) 1, ?_⟩
    intro x h
    change T x h = T (rho h x) 1
    rw [heq]
    simp [rho]

theorem isca_lift (T : CA) : LazyInvertibleGeneration.IsCA (lift T) := by
  apply (actual_equiv_iff _).mpr
  intro x h
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨g, rfl⟩ := phi.surjective h
  rw [← q_act, lift_apply, equiv, q_act, lift_apply]

def pull (T : Function.End Config) (hT : LazyInvertibleGeneration.IsCA T) : CA :=
  ⟨fun x => q.symm (T (q x)), by
    intro g x
    apply q.injective
    simp only [q.apply_symm_apply, q_act]
    exact (actual_equiv_iff T).mp hT (q x) (phi g)⟩

theorem lift_pull (T : Function.End Config) (hT : LazyInvertibleGeneration.IsCA T) :
    lift (pull T hT) = T := by
  funext x
  change q (q.symm (T (q (q.symm x)))) = T x
  rw [q.apply_symm_apply, q.apply_symm_apply]

theorem actual_lazy_iff (T : Function.End Config) : LazyInvertibleGeneration.IsLazy T ↔
    ∃ (S : Finset H) (p : Config), 1 ∈ S ∧ ∀ x g, T x g =
      if ∀ s ∈ S, x (s * g) = p s then !(x g) else x g := by
  constructor
  · rintro ⟨S, he, μ, p, hμ, hT⟩
    let p' : Config := fun s => if hs : s ∈ S then p ⟨s, hs⟩ else false
    refine ⟨S, p', he, ?_⟩
    intro x g
    have hm : (∀ s ∈ S, x (s * g) = p' s) ↔ (fun s : S => x (s.1 * g)) = p := by
      constructor
      · intro h; funext s; simpa [p', s.property] using h s.1 s.property
      · intro h s hs; simpa [p', hs] using congrFun h ⟨s, hs⟩
    rw [hT]
    by_cases h : (fun s : S => x (s.1 * g)) = p
    · rw [if_pos (hm.mpr h), h]
      have ha : μ p ≠ p ⟨1, he⟩ := fun hh => (hμ p).mp hh rfl
      have hc : x g = p ⟨1, he⟩ := by simpa using congrFun h ⟨1, he⟩
      rw [hc]
      revert ha
      generalize μ p = a
      generalize p ⟨1, he⟩ = b
      cases a <;> cases b <;> decide
    · rw [if_neg (fun hh => h (hm.mp hh)), (hμ _).mpr h]
      simp
  · rintro ⟨S, p, he, hT⟩
    let p' : S → Bool := fun s => p s.1
    let μ : (S → Bool) → Bool := fun z => if z = p' then !(z ⟨1, he⟩) else z ⟨1, he⟩
    refine ⟨S, he, μ, p', ?_, ?_⟩
    · intro z
      by_cases hz : z = p'
      · subst z; simp [μ]
      · simp [μ, hz]
    · intro x g
      rw [hT]
      have hm : (∀ s ∈ S, x (s * g) = p s) ↔ (fun s : S => x (s.1 * g)) = p' := by
        constructor
        · intro h; funext s; exact h s.1 s.property
        · intro h s hs; exact congrFun h ⟨s, hs⟩
      simp only [μ, ← hm, one_mul]

theorem lift_lazy_apply (S : Finset G) (p : Bits) (x : Config) (g : H) :
    lift (lazyMap S p) x g =
      if ∀ h ∈ S, x (phi h * g) = p h then !(x g) else x g := by
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨a, rfl⟩ := phi.surjective g
  rw [lift_apply]
  change encode ((lazyMap S p) y) (phi.symm (phi a)) = _
  rw [phi.symm_apply_apply]
  change encode (decode _) a = _
  rw [encode_decode]
  simp only [encode_act, e_gm, q, Equiv.coe_fn_mk, ← phi_mul, Equiv.symm_apply_apply]

theorem lazy_lift_iff (T : CA) : LazyInvertibleGeneration.IsLazy (lift T) ↔ T ∈ L := by
  rw [actual_lazy_iff]
  constructor
  · rintro ⟨S, p, he, hT⟩
    let S' := S.map phi.symm.toEmbedding
    let p' : Bits := fun g => p (phi g)
    have he' : e ∈ S' := by
      apply Finset.mem_map.mpr
      exact ⟨1, he, phi.injective (by simp [phi_e])⟩
    refine ⟨S', p', he', ?_⟩
    apply lift_injective
    funext x g
    rw [hT, lift_lazy_apply]
    congr 1
    apply propext
    constructor
    · intro h a ha
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ha
      simpa [p'] using h s hs
    · intro h s hs
      simpa [p'] using h (phi.symm s) (Finset.mem_map.mpr ⟨s, hs, rfl⟩)
  · rintro ⟨S, p, he, rfl⟩
    refine ⟨S.map phi.toEmbedding, fun h => p (phi.symm h), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨e, he, phi_e⟩
    · intro x g
      rw [lift_lazy_apply]
      congr 1
      apply propext
      constructor
      · intro h s hs
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hs
        simpa using h a ha
      · intro h a ha
        simpa using h (phi a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)

theorem invertible_lift_iff (T : CA) :
    LazyInvertibleGeneration.IsInvertibleCA (lift T) ↔ T ∈ ICA := by
  constructor
  · rintro ⟨_, R, _, hRT, hTR⟩
    constructor
    · intro x y h
      apply q.injective
      have hh := congrArg R (congrArg q h)
      rw [← lift_apply, ← lift_apply] at hh
      have hx := congrFun hRT (q x)
      have hy := congrFun hRT (q y)
      exact hx.symm.trans (hh.trans hy)
    · intro y
      refine ⟨q.symm (R (q y)), ?_⟩
      apply q.injective
      have hh := congrFun hTR (q y)
      change lift T (R (q y)) = q y at hh
      change q (T (q.symm (R (q y)))) = q y at hh
      exact hh
  · intro hT
    have hb : Function.Bijective (lift T) :=
      q.bijective.comp (hT.comp q.symm.bijective)
    let E : Config ≃ Config := Equiv.ofBijective (lift T) hb
    refine ⟨isca_lift T, (fun x => E.symm x), ?_, ?_, ?_⟩
    · apply (actual_equiv_iff _).mpr
      intro x h
      apply E.injective
      change lift T (E.symm (rho h x)) = lift T (rho h (E.symm x))
      exact (E.apply_symm_apply (rho h x)).trans
        ((congrArg (rho h) (E.apply_symm_apply x).symm).trans
          ((actual_equiv_iff _).mp (isca_lift T) (E.symm x) h).symm)
    · funext x
      exact E.symm_apply_apply x
    · funext x
      exact E.apply_symm_apply x

def generated : Submonoid (Function.End Config) :=
  Submonoid.closure ({T | LazyInvertibleGeneration.IsInvertibleCA T} ∪
    {T | LazyInvertibleGeneration.IsLazy T})

theorem lift_mem_generated (T : CA) (hT : T ∈ M) : lift T ∈ generated := by
  induction hT using Submonoid.closure_induction with
  | mem T h =>
    apply Submonoid.subset_closure
    rcases h with h | h
    · exact Or.inl ((invertible_lift_iff T).mpr h)
    · exact Or.inr ((lazy_lift_iff T).mpr h)
  | one => rw [map_one]; exact generated.one_mem
  | mul A B _ _ hA hB => rw [map_mul]; exact generated.mul_mem hA hB

theorem generated_representation (F : Function.End Config) (hF : F ∈ generated) :
    ∃ T : CA, T ∈ M ∧ lift T = F := by
  induction hF using Submonoid.closure_induction with
  | mem F h =>
    have hca : LazyInvertibleGeneration.IsCA F := by
      rcases h with h | ⟨S, _, μ, _, _, hF⟩
      · exact h.1
      · exact ⟨S, μ, hF⟩
    let T := pull F hca
    have hTF : lift T = F := lift_pull F hca
    refine ⟨T, Submonoid.subset_closure ?_, hTF⟩
    rcases h with h | h
    · exact Or.inl ((invertible_lift_iff T).mp (hTF.symm ▸ h))
    · exact Or.inr ((lazy_lift_iff T).mp (hTF.symm ▸ h))
  | one => exact ⟨1, M.one_mem, lift.map_one⟩
  | mul A B _ _ hA hB =>
    obtain ⟨A', hA', heA⟩ := hA
    obtain ⟨B', hB', heB⟩ := hB
    exact ⟨A' * B', M.mul_mem hA' hB', by rw [map_mul, heA, heB]⟩

theorem lift_membership_iff (T : CA) : lift T ∈ generated ↔ T ∈ M := by
  constructor
  · intro h
    obtain ⟨R, hR, he⟩ := generated_representation _ h
    exact lift_injective he ▸ hR
  · exact lift_mem_generated T

def freeSet (b : Bool) : Set X := {x | freeOrbit x = some b}
def pairSet (s : Fin 3) : Set X := {x | ∃ b, x = .p s b}
def constantSet : Set X := {x | ∃ b, x = .c b}

theorem freeSet_param : ∀ b x, x ∈ freeSet b ↔ ∃ g, x = .f b g := by
  change ∀ b x, freeOrbit x = some b ↔ ∃ g, x = .f b g
  decide

theorem image_freeSet (T : CA) (b : Bool) :
    T '' freeSet b = Set.range (fun g => act g (T (.f b e))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := (freeSet_param b x).mp hx
    exact ⟨g, (equiv T g (.f b e)).symm.trans (congrArg T (free_rep b g))⟩
  · rintro ⟨g, rfl⟩
    refine ⟨.f b g, (freeSet_param b _).mpr ⟨g, rfl⟩, ?_⟩
    rw [← free_rep b g, equiv]

theorem orbit_eq_freeSet (x : X) (b : Bool) :
    Set.range (fun g => act g x) = freeSet b ↔ freeOrbit x = some b := by
  have h : ∀ x b,
      (∀ y, (∃ g, act g x = y) ↔ freeOrbit y = some b) ↔ freeOrbit x = some b := by decide
  rw [Set.ext_iff]
  exact h x b

theorem merges_iff_orbit_images (T : CA) : Merges T ↔
    ∃ b, T '' freeSet false = freeSet b ∧ T '' freeSet true = freeSet b := by
  simp only [image_freeSet, orbit_eq_freeSet, Merges]

theorem witness_iff_sets (T : X → X) : Witness T ↔
    ∃ s b, ∀ x ∈ constantSet ∪ pairSet s, T x = .c b := by
  constructor
  · rintro ⟨s, b, h0, h1, hp0, hp1⟩
    refine ⟨s, b, ?_⟩
    intro x hx
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> cases a <;> assumption
  · rintro ⟨s, b, h⟩
    exact ⟨s, b, h _ (Or.inl ⟨false, rfl⟩), h _ (Or.inl ⟨true, rfl⟩),
      h _ (Or.inr ⟨false, rfl⟩), h _ (Or.inr ⟨true, rfl⟩)⟩

def weight (x : Config) : Nat := (Finset.univ.filter fun h => x h = true).card
def weightSet (n : Nat) : Set Config := {x | weight x = n}
def constants : Set Config := {x | ∃ b, x = fun _ => b}
def orbit (x : Config) : Set Config := Set.range (fun h => rho h x)
def orbitFinset (x : Config) : Finset Config := Finset.univ.image (fun h => rho h x)

theorem q_free_weight : ∀ b x, x ∈ freeSet b ↔ q x ∈ weightSet (if b then 3 else 1) := by
  dsimp only [freeSet, weightSet, Set.mem_setOf_eq, weight]
  decide

theorem q_freeSet (b : Bool) : q '' freeSet b = weightSet (if b then 3 else 1) := by
  ext y
  obtain ⟨x, rfl⟩ := q.surjective y
  rw [Set.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (q_free_weight b x).mp (q.injective he ▸ ha)
  · intro h
    exact ⟨x, (q_free_weight b x).mpr h, rfl⟩

theorem q_constants : q '' constantSet = constants := by
  ext y
  constructor
  · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨.c b, ⟨b, rfl⟩, rfl⟩

theorem pair_orbit (s : Fin 3) (b : Bool) : orbit (q (.p s b)) = q '' pairSet s := by
  ext y
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨g, rfl⟩ := phi.surjective h
    change rho (phi g) (q (.p s b)) ∈ q '' pairSet s
    rw [← q_act]
    exact ⟨act g (.p s b), ⟨xor b (character s g), rfl⟩, rfl⟩
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    have h : ∀ s a b, ∃ g, act g (.p s b) = .p s a := by decide
    obtain ⟨g, hg⟩ := h s a b
    refine ⟨phi g, ?_⟩
    change rho (phi g) (q (.p s b)) = q (.p s a)
    rw [← q_act, hg]

theorem two_point_classification (x : Config) :
    (orbitFinset x).card = 2 ↔ ∃ s b, x = q (.p s b) := by
  obtain ⟨y, rfl⟩ := q.surjective x
  exact (by decide : ∀ y : X,
    (orbitFinset (q y)).card = 2 ↔ ∃ s b, q y = q (.p s b)) y

theorem q_image (T : CA) (S : Set X) : lift T '' (q '' S) = q '' (T '' S) := by
  change (fun x => lift T x) '' (q '' S) = q '' ((fun x => T x) '' S)
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact lift_apply T x

theorem actual_merges_iff (T : CA) : Merges T ↔
    ∃ b : Bool, lift T '' weightSet 1 = weightSet (if b then 3 else 1) ∧
      lift T '' weightSet 3 = weightSet (if b then 3 else 1) := by
  rw [merges_iff_orbit_images]
  have hinj := Set.image_injective.mpr q.injective
  have h0 : q '' freeSet false = weightSet 1 := q_freeSet false
  have h1 : q '' freeSet true = weightSet 3 := q_freeSet true
  constructor
  · rintro ⟨b, hb0, hb1⟩
    refine ⟨b, ?_, ?_⟩
    · rw [← h0, q_image, hb0, q_freeSet]
    · rw [← h1, q_image, hb1, q_freeSet]
  · rintro ⟨b, hb0, hb1⟩
    refine ⟨b, hinj ?_, hinj ?_⟩
    · rw [← q_image, h0, q_freeSet]
      exact hb0
    · rw [← q_image, h1, q_freeSet]
      exact hb1

theorem actual_witness_iff (T : CA) : Witness T ↔
    ∃ (x : Config) (b : Bool), (orbitFinset x).card = 2 ∧
      lift T '' (constants ∪ orbit x) = {fun _ => b} := by
  change Witness (fun x => T x) ↔ _
  rw [witness_iff_sets (fun x => T x)]
  constructor
  · rintro ⟨s, b, h⟩
    refine ⟨q (.p s false), b, (two_point_classification _).mpr ⟨s, false, rfl⟩, ?_⟩
    rw [pair_orbit, ← q_constants, ← Set.image_union, q_image]
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨T (.c false), ⟨.c false, Or.inl ⟨false, rfl⟩, rfl⟩,
        by rw [h _ (Or.inl ⟨false, rfl⟩)]; rfl⟩
    · rintro z ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      rw [h a ha]
      rfl
  · rintro ⟨x, b, hx, h⟩
    obtain ⟨s, a, rfl⟩ := (two_point_classification x).mp hx
    refine ⟨s, b, ?_⟩
    intro y hy
    apply q.injective
    change q (T y) = q (.c b)
    have hmem : lift T (q y) ∈ lift T '' (constants ∪ orbit (q (.p s a))) := by
      apply Set.mem_image_of_mem
      rw [pair_orbit, ← q_constants, ← Set.image_union]
      exact Set.mem_image_of_mem q hy
    rw [h] at hmem
    exact (by simpa only [lift_apply, Set.mem_singleton_iff] using hmem :
      q (T y) = fun _ => b)

/-- The public structural membership criterion on actual binary configurations. -/
theorem membership_iff (T : Function.End Config) (hT : LazyInvertibleGeneration.IsCA T) :
    T ∈ Submonoid.closure ({F | LazyInvertibleGeneration.IsInvertibleCA F} ∪
      {F | LazyInvertibleGeneration.IsLazy F}) ↔
    ((∃ b : Bool, T '' weightSet 1 = weightSet (if b then 3 else 1) ∧
      T '' weightSet 3 = weightSet (if b then 3 else 1)) →
      ∃ (x : Config) (b : Bool), (orbitFinset x).card = 2 ∧
        T '' (constants ∪ orbit x) = {fun _ => b}) := by
  let R := pull T hT
  have hR : lift R = T := lift_pull T hT
  change T ∈ generated ↔ _
  rw [← hR, lift_membership_iff]
  have hc : R ∈ M ↔ Criterion R :=
    ⟨membership_implies_criterion R, criterion_implies_membership R⟩
  rw [hc]
  exact imp_congr (actual_merges_iff R) (actual_witness_iff R)

end D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization
