/- GID: D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativePostClockInverse
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite rational recovery of post-clock native addressed histories. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Local inverse of the actual zero-extended, post-clock native field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativePostClockInverse

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (replace)
open Geometry.NativeMaterialRootRecognition (D material neighbors root_mem material_nodup)
open Geometry.NativeGuardedLeafRepair (Call Value zeroExtend run)

/-- The literal new local term; true is promotion and false is splitting. -/
def replacement (b : Bool) : Source :=
  if b then .of false else .mul (.of false) (.of true)

/-- The fresh cells, including the new left marker but excluding every old cell. -/
def fresh (b : Bool) (p : Address) : List Address :=
  if b then [p ++ [false]] else [p ++ [false, false], p ++ [true]]

private theorem fresh_cons (b d : Bool) (p : Address) :
    fresh b (d :: p) = (fresh b p).map (d :: ·) := by
  cases b <;> rfl

/-- Structural data of one edit, stated on the original material and logical carriers. -/
private theorem edit_structure (b : Bool) (p : Address) (t : Source)
    (h : subtree p t = some (.of b)) :
    (∀ q, q ∈ material (replace t p (replacement b)) ↔
      q ∈ material t ∨ q ∈ fresh b p) ∧
    (∀ q ∈ fresh b p, q ∉ material t) ∧
    (∀ q ∈ fresh b p, ∃ r ∈ material t,
      r ∈ neighbors (replace t p (replacement b)) q) ∧
    subtree p (replace t p (replacement b)) = some (replacement b) ∧
    replace (replace t p (replacement b)) p (.of b) = t := by
  induction p generalizing t with
  | nil =>
      have ht : t = .of b := Option.some.inj h
      subst t
      cases b <;>
        simp [fresh, replacement, replace, subtree, material, neighbors,
          Geometry.NativeMaterialRootRecognition.children, readout, or_assoc]
  | cons d p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases d with
          | false =>
              obtain ⟨hm, hf, hn, hs, hc⟩ := ih l h
              refine ⟨?_, ?_, ?_, hs, ?_⟩
              · intro q
                cases q with
                | nil => simp [replace, material, fresh_cons]
                | cons d q =>
                    cases d <;> simp [replace, material, fresh_cons, List.mem_map, hm]
              · intro q hq
                simp only [fresh_cons, List.mem_map] at hq
                obtain ⟨q, hq, rfl⟩ := hq
                simpa [material, List.mem_map] using hf q hq
              · intro q hq
                simp only [fresh_cons, List.mem_map] at hq
                obtain ⟨q, hq, rfl⟩ := hq
                obtain ⟨u, hu, hn⟩ := hn q hq
                refine ⟨false :: u, ?_, ?_⟩
                · simp [material, List.mem_map, hu]
                · simp only [replace, Geometry.NativeMaterialRootRecognition.neighbors_cons]
                  exact List.mem_append_left _ (List.mem_map.mpr ⟨u, hn, rfl⟩)
              · simpa only [replace] using congrArg (fun s : Source => FreeMagma.mul s r) hc
          | true =>
              obtain ⟨hm, hf, hn, hs, hc⟩ := ih r h
              refine ⟨?_, ?_, ?_, hs, ?_⟩
              · intro q
                cases q with
                | nil => simp [replace, material, fresh_cons]
                | cons d q =>
                    cases d <;> simp [replace, material, fresh_cons, List.mem_map, hm]
              · intro q hq
                simp only [fresh_cons, List.mem_map] at hq
                obtain ⟨q, hq, rfl⟩ := hq
                simpa [material, List.mem_map] using hf q hq
              · intro q hq
                simp only [fresh_cons, List.mem_map] at hq
                obtain ⟨q, hq, rfl⟩ := hq
                obtain ⟨u, hu, hn⟩ := hn q hq
                refine ⟨true :: u, ?_, ?_⟩
                · simp [material, List.mem_map, hu]
                · simp only [replace, Geometry.NativeMaterialRootRecognition.neighbors_cons]
                  exact List.mem_append_left _ (List.mem_map.mpr ⟨u, hn, rfl⟩)
              · simpa only [replace] using congrArg (fun s : Source => FreeMagma.mul l s) hc

/-- Coordinates are the finite, explicitly listed native material support. -/
abbrev Coordinate (t : Source) := {p : Address // p ∈ (material t).toFinset}

local instance coordinates (t : Source) : Fintype (Coordinate t) :=
  Finset.fintypeCoeSort (material t).toFinset

abbrev Field (t : Source) := Coordinate t → ℚ

/-- Literal zero inclusion, with no old value attached to a fresh cell. -/
def zeroInclude (t u : Source) (x : Field t) : Field u :=
  fun p => if h : p.val ∈ (material t).toFinset then x ⟨p.val, h⟩ else 0

/-- The actual rational diagonal plus unit material adjacency. -/
def clock (a c : ℚ) (t : Source) : Matrix (Coordinate t) (Coordinate t) ℚ :=
  fun p q => (if p = q then a else 0) +
    (if q.val ∈ neighbors t p.val then c else 0)

def tick (a c : ℚ) (t : Source) (x : Field t) : Field t :=
  (clock a c t).mulVec x

/-- Finite determinant and adjugate arithmetic, using the rational inverse operation. -/
def untick (a c : ℚ) (t : Source) (x : Field t) : Field t :=
  ((clock a c t).det⁻¹ • (clock a c t).adjugate).mulVec x

private theorem untick_tick (a c : ℚ) (t : Source) (x : Field t)
    (h : (clock a c t).det ≠ 0) : untick a c t (tick a c t x) = x := by
  have hm : ((clock a c t).det⁻¹ • (clock a c t).adjugate) * clock a c t = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ h, one_smul]
  unfold untick tick
  rw [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]

private theorem tick_positive (a c : ℚ) (ha : 0 < a) (hc : 0 < c)
    (b : Bool) (p : Address) (t : Source) (h : subtree p t = some (.of b))
    (x : Field t) (hx : ∀ q, 0 < x q) :
    ∀ q, 0 < tick a c (replace t p (replacement b))
      (zeroInclude t (replace t p (replacement b)) x) q := by
  let u := replace t p (replacement b)
  obtain ⟨hm, hf, hn, _, _⟩ := edit_structure b p t h
  have hi : ∀ q : Coordinate u, 0 ≤ zeroInclude t u x q := by
    intro q
    unfold zeroInclude
    split
    · exact (hx _).le
    · exact le_rfl
  have hm0 : ∀ q r : Coordinate u, 0 ≤ clock a c u q r := by
    intro q r
    unfold clock
    exact add_nonneg (by split <;> positivity) (by split <;> positivity)
  intro q
  apply (Finset.sum_pos_iff_of_nonneg (fun r _ => mul_nonneg (hm0 q r) (hi r))).mpr
  rcases (hm q.val).mp (List.mem_toFinset.mp q.property) with hq | hq
  · refine ⟨q, Finset.mem_univ _, mul_pos ?_ ?_⟩
    · have : 0 ≤ (if q.val ∈ neighbors u q.val then c else 0) := by split <;> positivity
      simpa only [clock, ↓reduceIte] using add_pos_of_pos_of_nonneg ha this
    · simpa [zeroInclude, List.mem_toFinset.mpr hq] using hx ⟨q.val, List.mem_toFinset.mpr hq⟩
  · obtain ⟨r, hr, hqr⟩ := hn q.val hq
    let r' : Coordinate u := ⟨r, List.mem_toFinset.mpr ((hm r).mpr (Or.inl hr))⟩
    refine ⟨r', Finset.mem_univ _, mul_pos ?_ ?_⟩
    · have : 0 ≤ (if q = r' then a else 0) := by split <;> positivity
      change r'.val ∈ neighbors u q.val at hqr
      simpa only [clock, ite_eq_left hqr] using add_pos_of_nonneg_of_pos this hc
    · simpa [zeroInclude, r', List.mem_toFinset.mpr hr] using hx ⟨r, List.mem_toFinset.mpr hr⟩

/-- The two fields carried at a returned encoding cut are entirely current data. -/
abbrev Endpoint := (t : Source) × Field t

def kind : Call → Bool
  | .promote _ => true
  | .split _ => false

def address : Call → Address
  | .promote p | .split p => p

def edited (t : Source) (g : Call) : Source :=
  replace t (address g) (replacement (kind g))

def appendEndpoint (a c : ℚ) (e : Endpoint) (g : Call) : Endpoint :=
  ⟨edited e.1 g, tick a c (edited e.1 g) (zeroInclude e.1 (edited e.1 g) e.2)⟩

/-- A pure encoding success, retaining the original guarded logical test. -/
def forward (a c : ℚ) (e : Endpoint) (g : Call) : Option Endpoint :=
  if subtree (address g) e.1 = some (.of (kind g)) then
    some (appendEndpoint a c e g) else none

def replay (a c : ℚ) : Endpoint → List Call → Option Endpoint
  | e, [] => some e
  | e, g :: w => (forward a c e g).bind (fun u => replay a c u w)

def origin : Endpoint := ⟨.of true, fun _ => 1⟩

def encode (a c : ℚ) : List Call → Option Endpoint := replay a c origin

/-- The exact finite zero support; no putative old history is consulted. -/
def zeros (t : Source) (x : Field t) : Finset Address :=
  (Finset.univ.filter (fun p : Coordinate t => x p = 0)).image Subtype.val

private theorem zeroInclude_zeros (b : Bool) (p : Address) (t : Source)
    (h : subtree p t = some (.of b)) (x : Field t) (hx : ∀ q, 0 < x q) :
    zeros (replace t p (replacement b))
      (zeroInclude t (replace t p (replacement b)) x) = (fresh b p).toFinset := by
  obtain ⟨hm, hf, _, _, _⟩ := edit_structure b p t h
  ext q
  simp only [zeros, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases (hm r.val).mp (List.mem_toFinset.mp r.property) with ho | hn
    · have hh : zeroInclude t (replace t p (replacement b)) x r =
          x ⟨r.val, List.mem_toFinset.mpr ho⟩ := by simp [zeroInclude, ho]
      exact False.elim ((ne_of_gt (hx _)) (hh.symm.trans hr))
    · exact hn
  · intro hq
    let r : Coordinate (replace t p (replacement b)) :=
      ⟨q, List.mem_toFinset.mpr ((hm q).mpr (Or.inr hq))⟩
    refine ⟨r, ?_, rfl⟩
    simp [zeroInclude, r, hf q hq]

private theorem suffix_ne (p q : Address) : p ++ [false] ≠ q ++ [true] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

private theorem fresh_unique (b d : Bool) (p q : Address)
    (h : (fresh b p).toFinset = (fresh d q).toFinset) : b = d ∧ p = q := by
  cases b <;> cases d
  · have hr : p ++ [true] ∈ (fresh false q).toFinset := by
      rw [← h]
      simp [fresh]
    have hr' : p ++ [true] = q ++ [false, false] ∨ p = q := by
      simpa [fresh] using hr
    rcases hr' with hr | hr
    · exact False.elim (suffix_ne (q ++ [false]) p (by simpa [List.append_assoc] using hr.symm))
    · exact ⟨rfl, hr⟩
  · have hr : p ++ [true] ∈ (fresh true q).toFinset := by rw [← h]; simp [fresh]
    simp [fresh] at hr
  · have hr : q ++ [true] ∈ (fresh true p).toFinset := by rw [h]; simp [fresh]
    simp [fresh] at hr
  · have : p ++ [false] = q ++ [false] := by simpa [fresh] using h
    exact ⟨rfl, List.append_cancel_right this⟩

private theorem call_unique (g h : Call)
    (he : (fresh (kind g) (address g)).toFinset =
      (fresh (kind h) (address h)).toFinset) : g = h := by
  have hh := fresh_unique (kind g) (kind h) (address g) (address h) he
  cases g <;> cases h <;> simp_all [kind, address]

def candidates (t : Source) : List Call :=
  (material t).flatMap (fun q => [.promote q.dropLast, .split q.dropLast])

def lastEvent (t : Source) (z : Field t) : Option Call :=
  (candidates t).find? (fun g => decide (
    zeros t z = (fresh (kind g) (address g)).toFinset ∧
    subtree (address g) t = some (replacement (kind g))))

private theorem last_event (t : Source) (g : Call)
    (h : subtree (address g) t = some (.of (kind g)))
    (x : Field t) (hx : ∀ q, 0 < x q) :
    lastEvent (edited t g) (zeroInclude t (edited t g) x) = some g := by
  obtain ⟨hm, _, _, hs, _⟩ := edit_structure (kind g) (address g) t h
  have hz := zeroInclude_zeros (kind g) (address g) t h x hx
  have hg : g ∈ candidates (edited t g) := by
    cases g with
    | promote p =>
        have hf : p ++ [false] ∈ material (edited t (.promote p)) :=
          (hm _).mpr (Or.inr (by simp [kind, address, fresh]))
        exact List.mem_flatMap.mpr ⟨p ++ [false], hf, by simp⟩
    | split p =>
        have hf : p ++ [true] ∈ material (edited t (.split p)) :=
          (hm _).mpr (Or.inr (by simp [kind, address, fresh]))
        exact List.mem_flatMap.mpr ⟨p ++ [true], hf, by simp⟩
  have hp : decide (zeros (edited t g) (zeroInclude t (edited t g) x) =
      (fresh (kind g) (address g)).toFinset ∧
      subtree (address g) (edited t g) = some (replacement (kind g))) = true := by
    exact decide_eq_true ⟨hz, hs⟩
  have hex : (lastEvent (edited t g) (zeroInclude t (edited t g) x)).isSome := by
    unfold lastEvent
    exact List.find?_isSome.mpr ⟨g, hg, hp⟩
  cases he : lastEvent (edited t g) (zeroInclude t (edited t g) x) with
  | none => simp [he] at hex
  | some g' =>
      have he' := he
      unfold lastEvent at he'
      have hp' := List.find?_some he'
      have hh : zeros (edited t g) (zeroInclude t (edited t g) x) =
          (fresh (kind g') (address g')).toFinset ∧
          subtree (address g') (edited t g) = some (replacement (kind g')) :=
        of_decide_eq_true hp'
      have heq : g = g' := call_unique g g' (hz.symm.trans hh.1)
      simpa [heq] using he

def collapse (t : Source) (g : Call) : Source :=
  replace t (address g) (.of (kind g))

/-- One finite local reverse step: untick, identify fresh zeros, collapse, restrict. -/
def predecessor (a c : ℚ) (e : Endpoint) : Option (Endpoint × Call) := do
  let z := untick a c e.1 e.2
  let g ← lastEvent e.1 z
  pure (⟨collapse e.1 g, zeroInclude e.1 (collapse e.1 g) z⟩, g)

private theorem predecessor_append (a c : ℚ) (e : Endpoint) (g : Call)
    (he : subtree (address g) e.1 = some (.of (kind g)))
    (hx : ∀ q, 0 < e.2 q) (hi : (clock a c (edited e.1 g)).det ≠ 0) :
    predecessor a c (appendEndpoint a c e g) = some (e, g) := by
  obtain ⟨hm, _, _, _, hc⟩ := edit_structure (kind g) (address g) e.1 he
  have hz := untick_tick a c (edited e.1 g) (zeroInclude e.1 (edited e.1 g) e.2) hi
  have hl := last_event e.1 g he e.2 hx
  have hback (v : Source) (hv : v = e.1) :
      (⟨v, zeroInclude (edited e.1 g) v
        (zeroInclude e.1 (edited e.1 g) e.2)⟩ : Endpoint) = e := by
    subst v
    have hf : zeroInclude (edited e.1 g) e.1
        (zeroInclude e.1 (edited e.1 g) e.2) = e.2 := by
      funext q
      have hq : q.val ∈ (material (edited e.1 g)).toFinset :=
        List.mem_toFinset.mpr ((hm q.val).mpr (Or.inl (List.mem_toFinset.mp q.property)))
      simp [zeroInclude, hq, q.property]
    exact congrArg (fun y : Field e.1 => (⟨e.1, y⟩ : Endpoint)) hf
  unfold predecessor appendEndpoint
  dsimp only
  rw [hz, hl]
  change some (⟨collapse (edited e.1 g) g,
    zeroInclude (edited e.1 g) (collapse (edited e.1 g) g)
      (zeroInclude e.1 (edited e.1 g) e.2)⟩, g) = some (e, g)
  rw [hback (collapse (edited e.1 g) g) hc]

/-- Fuel is measured in current material vertices; it is not a supplied history bound. -/
def decodeFuel (a c : ℚ) : ℕ → Endpoint → Option (List Call)
  | 0, _ => none
  | n + 1, e =>
      if e.1 = .of true then some [] else do
        let (u, g) ← predecessor a c e
        let w ← decodeFuel a c n u
        pure (w ++ [g])

def decode (a c : ℚ) (e : Endpoint) : Option (List Call) :=
  decodeFuel a c (material e.1).length e

private inductive Encoded (a c : ℚ) : List Call → Endpoint → Prop
  | seed : Encoded a c [] origin
  | append {w : List Call} {e : Endpoint} (hw : Encoded a c w e) (g : Call)
      (he : subtree (address g) e.1 = some (.of (kind g))) :
      Encoded a c (w ++ [g]) (appendEndpoint a c e g)

private theorem reached_replay (a c : ℚ) {w : List Call} {e : Endpoint}
    (hw : Encoded a c w e) {v : List Call} {u : Endpoint}
    (hv : replay a c e v = some u) : Encoded a c (w ++ v) u := by
  induction v generalizing w e with
  | nil =>
      have hu : e = u := Option.some.inj hv
      simpa [hu] using hw
  | cons g v ih =>
      unfold replay forward at hv
      split at hv
      next he =>
        simp only [Option.bind_some] at hv
        simpa [List.append_assoc] using ih (Encoded.append hw g he) hv
      next he => simp at hv

private theorem encoded_of_encode (a c : ℚ) (w : List Call) (e : Endpoint)
    (h : encode a c w = some e) : Encoded a c w e := by
  simpa using reached_replay a c (Encoded.seed) h

private theorem replay_append (a c : ℚ) (e : Endpoint) (w v : List Call) :
    replay a c e (w ++ v) = (replay a c e w).bind (fun u => replay a c u v) := by
  induction w generalizing e with
  | nil => rfl
  | cons g w ih =>
      simp only [List.cons_append, replay]
      cases forward a c e g <;> simp [ih]

private theorem encode_of_encoded (a c : ℚ) {w : List Call} {e : Endpoint}
    (hw : Encoded a c w e) : encode a c w = some e := by
  induction hw with
  | seed => rfl
  | @append w e hw g he ih =>
      change replay a c origin (w ++ [g]) = _
      rw [replay_append]
      change (encode a c w).bind _ = _
      rw [ih]
      simp [replay, forward, he]

private theorem replay_term (a c : ℚ) (e : Endpoint) (w : List Call) :
    (replay a c e w).map (fun u => u.1) = run e.1 w := by
  have hab : (FreeMagma.of false : Source) ≠ .of true := by decide
  have hba : (FreeMagma.of true : Source) ≠ .of false := by decide
  induction w generalizing e with
  | nil => rfl
  | cons g w ih =>
      cases g with
      | promote p =>
          cases hs : subtree p e.1 with
          | none => simp [replay, forward, kind, address, hs, run]
          | some t =>
              cases t with
              | of b => cases b <;>
                  simp [replay, forward, kind, address, hs, run, ih, appendEndpoint,
                    edited, replacement, hab]
              | mul l r => simp [replay, forward, kind, address, hs, run]
      | split p =>
          cases hs : subtree p e.1 with
          | none => simp [replay, forward, kind, address, hs, run]
          | some t =>
              cases t with
              | of b => cases b <;>
                  simp [replay, forward, kind, address, hs, run, ih, appendEndpoint,
                    edited, replacement, hba]
              | mul l r => simp [replay, forward, kind, address, hs, run]

private theorem encoded_trace (a c : ℚ) {w : List Call} {e : Endpoint}
    (hw : Encoded a c w e) : run (.of true) w = some e.1 := by
  have hh := congrArg (fun o : Option Endpoint => o.map (fun u => u.1))
    (encode_of_encoded a c hw)
  simpa only [encode, replay_term, Option.map_some, origin] using hh

private theorem singleton_run (t : Source) (g : Call)
    (h : subtree (address g) t = some (.of (kind g))) :
    run t [g] = some (edited t g) := by
  cases g <;> simp_all [run, kind, address, edited, replacement]

private theorem edit_growth (t : Source) (ht : D t) (g : Call)
    (h : subtree (address g) t = some (.of (kind g))) :
    D (edited t g) ∧ (material t).length < (material (edited t g)).length := by
  have hr := singleton_run t g h
  have hd := Geometry.NativeGuardedLeafRepair.run_preserves_D ht hr
  have hh := Geometry.NativeGuardedLeafRepair.history_card
    (⟨edited t g, [g], hr, hd⟩ : Geometry.NativeGuardedLeafRepair.History t)
  change (material (edited t g)).toFinset.card = (material t).toFinset.card +
    Geometry.NativeGuardedLeafRepair.promotions [g] +
      2 * Geometry.NativeGuardedLeafRepair.splits [g] at hh
  rw [Geometry.NativeGuardedLeafRepair.material_card,
    Geometry.NativeGuardedLeafRepair.material_card] at hh
  refine ⟨hd, ?_⟩
  cases g <;>
    simp [Geometry.NativeGuardedLeafRepair.promotions,
      Geometry.NativeGuardedLeafRepair.splits] at hh <;>
    omega

private theorem encoded_invariants (a c : ℚ) (ha : 0 < a) (hc : 0 < c)
    (hinv : ∀ (v : List Call) (t : Source), run (.of true) v = some t →
      (clock a c t).det ≠ 0)
    {w : List Call} {e : Endpoint} (hw : Encoded a c w e) :
    D e.1 ∧ (∀ q, 0 < e.2 q) ∧
      ∀ n, (material e.1).length ≤ n → decodeFuel a c n e = some w := by
  induction hw with
  | seed =>
      refine ⟨?_, ?_, ?_⟩
      · intro p
        cases p <;> simp [origin, readout]
      · intro q; exact zero_lt_one
      · intro n hn
        cases n with
        | zero => simp [origin, material] at hn
        | succ n => rfl
  | @append w e hw g he ih =>
      obtain ⟨hd, hg⟩ := edit_growth e.1 ih.1 g he
      have hi := hinv (w ++ [g]) (edited e.1 g)
        (encoded_trace a c (Encoded.append hw g he))
      refine ⟨hd, tick_positive a c ha hc (kind g) (address g) e.1 he e.2 ih.2.1, ?_⟩
      intro n hn
      have hn' : (material (edited e.1 g)).length ≤ n := hn
      have hn0 : 0 < (material e.1).length :=
        List.length_pos_iff.mpr (by
          intro hem
          have hm := root_mem e.1
          simp [hem] at hm)
      have hne : (appendEndpoint a c e g).1 ≠ .of true := by
        intro hh
        have hm : (material (edited e.1 g)).length = 1 := by
          change edited e.1 g = .of true at hh
          rw [hh]
          rfl
        omega
      cases n with
      | zero => omega
      | succ n =>
          simp only [decodeFuel, ite_eq_right hne]
          rw [predecessor_append a c e g he ih.2.1 hi]
          change (decodeFuel a c n e).bind (fun u => some (u ++ [g])) = some (w ++ [g])
          rw [ih.2.2 n (by omega)]
          rfl

private theorem replay_exists (a c : ℚ) (e : Endpoint) (w : List Call) (t : Source)
    (h : run e.1 w = some t) :
    ∃ x : Field t, replay a c e w = some ⟨t, x⟩ := by
  induction w generalizing e with
  | nil =>
      have he : e.1 = t := Option.some.inj h
      subst t
      exact ⟨e.2, rfl⟩
  | cons g w ih =>
      cases g with
      | promote p =>
          unfold run at h
          split at h <;> try contradiction
          next hs =>
            obtain ⟨x, hx⟩ := ih (appendEndpoint a c e (.promote p)) h
            refine ⟨x, ?_⟩
            simpa [replay, forward, address, kind, hs] using hx
      | split p =>
          unfold run at h
          split at h <;> try contradiction
          next hs =>
            obtain ⟨x, hx⟩ := ih (appendEndpoint a c e (.split p)) h
            refine ⟨x, ?_⟩
            simpa [replay, forward, address, kind, hs] using hx

/-- The full post-clock image has a finite local inverse, including its earned empty origin. -/
theorem postclock_inverse (a c : ℚ) (ha : 0 < a) (hc : 0 < c)
    (hinv : ∀ (v : List Call) (t : Source), run (.of true) v = some t →
      (clock a c t).det ≠ 0) :
    (∀ (w : List Call) (t : Source), run (.of true) w = some t →
      ∃ x : Field t, encode a c w = some ⟨t, x⟩ ∧
        decode a c ⟨t, x⟩ = some w ∧ ∀ q, 0 < x q) ∧
    (∀ (w : List Call) (e : Endpoint), encode a c w = some e →
      decode a c e = some w) ∧
    (∀ e : Endpoint, (∃ w, encode a c w = some e) →
      (decode a c e).bind (encode a c) = some e) ∧
    (∀ (w v : List Call) (e : Endpoint), encode a c w = some e →
      encode a c v = some e → w = v) ∧
    (∀ (w : List Call) (e : Endpoint) (g : Call), encode a c w = some e →
      subtree (address g) e.1 = some (.of (kind g)) →
      predecessor a c (appendEndpoint a c e g) = some (e, g) ∧
        (material e.1).length < (material (edited e.1 g)).length) := by
  have hdec : ∀ (w : List Call) (e : Endpoint), encode a c w = some e →
      decode a c e = some w := by
    intro w e he
    exact (encoded_invariants a c ha hc hinv (encoded_of_encode a c w e he)).2.2 _ le_rfl
  refine ⟨?_, hdec, ?_, ?_, ?_⟩
  · intro w t hw
    obtain ⟨x, hx⟩ := replay_exists a c origin w t hw
    have hh := encoded_invariants a c ha hc hinv (encoded_of_encode a c w ⟨t, x⟩ hx)
    exact ⟨x, hx, hdec w ⟨t, x⟩ hx, hh.2.1⟩
  · rintro e ⟨w, hw⟩
    rw [hdec w e hw]
    exact hw
  · intro w v e hw hv
    exact Option.some.inj ((hdec w e hw).symm.trans (hdec v e hv))
  · intro w e g hw hg
    have hh := encoded_invariants a c ha hc hinv (encoded_of_encode a c w e hw)
    have hd := edit_growth e.1 hh.1 g hg
    exact ⟨predecessor_append a c e g hg hh.2.1 (hinv (w ++ [g]) _
      (encoded_trace a c (Encoded.append (encoded_of_encode a c w e hw) g hg))), hd.2⟩

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativePostClockInverse
