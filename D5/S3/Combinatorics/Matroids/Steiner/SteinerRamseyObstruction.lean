/- GID: D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A fixed binary fibre misses joint switch maxima on some finite power. -/

import D5.S3.Combinatorics.GroupWords.NathansonProblem9
import D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschSwitchCount
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! Four coordinate faces give monochromatic Pasch blocks in a finite power. -/

namespace D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction

open Filter

open SimpleGraph Function
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
open D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
open D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschSwitchCount
open scoped symmDiff

private theorem finiteRamseyPrefix {A : Type*} [Finite A] (arity size : ℕ) :
    ∃ n : ℕ, ∀ color : Finset ℕ → A,
      ∃ core : Finset ℕ, core ⊆ Finset.range n ∧ core.card = size ∧
        ∃ value : A, ∀ face ⊆ core, face.card = arity → color face = value := by
  classical
  let mono (color : Finset ℕ → A) (core : Finset ℕ) :=
    ∃ value : A, ∀ face ⊆ core, face.card = arity → color face = value
  change ∃ n : ℕ, ∀ color : Finset ℕ → A,
    ∃ core : Finset ℕ, core ⊆ Finset.range n ∧ core.card = size ∧ mono color core
  by_contra failure
  push Not at failure
  choose bad rejects using failure
  let tail := Ultrafilter.of (atTop : Filter ℕ)
  have stableColor (face : Finset ℕ) :
      ∃ value : A, ∀ᶠ n in (tail : Filter ℕ), bad n face = value := by
    obtain ⟨value, mapped⟩ := (tail.map fun n => bad n face).eq_pure_of_finite
    refine ⟨value, ?_⟩
    change {value} ∈ ((tail.map (fun n => bad n face) : Ultrafilter A) : Filter A)
    rw [mapped]
    simp
  choose limit eventual using stableColor
  obtain ⟨infiniteCore, _, infinite, value, monochromatic⟩ :=
    infinite_ramsey arity limit Set.infinite_univ
  obtain ⟨core, subset, card⟩ := infinite.exists_subset_card_eq size
  have inPrefix : ∀ᶠ n in (tail : Filter ℕ), core ⊆ Finset.range n :=
    (Ultrafilter.of_le (atTop : Filter ℕ))
      ((eventually_ge_atTop (core.sup id + 1)).mono fun n hn x hx =>
        Finset.mem_range.mpr ((Nat.lt_succ_of_le (Finset.le_sup hx)).trans_le hn))
  have agrees (checks : Finset (Finset ℕ)) :
      ∀ᶠ n in (tail : Filter ℕ), ∀ face ∈ checks, bad n face = limit face := by
    induction checks using Finset.induction_on with
    | empty => simp
    | insert face _ fresh ih =>
      filter_upwards [eventual face, ih] with n first rest face' inChecks
      rcases Finset.mem_insert.mp inChecks with rfl | old
      · exact first
      · exact rest _ old
  obtain ⟨n, inside, same⟩ := (inPrefix.and (agrees core.powerset)).exists
  apply rejects n core inside card
  exact ⟨value, fun face contained faces =>
    (same face (Finset.mem_powerset.mpr contained)).trans
      (monochromatic face (fun _ hx => subset (contained hx)) faces)⟩

private def supportPoint {L : Type*} (n : ℕ) (e t : L) (s : Finset ℕ) : Fin n → L :=
  fun i => if i.val ∈ s then t else e

private theorem supportPoint_mul {L : Type*} [Mul L] (n : ℕ) (e t : L)
    (ee : e * e = e) (et : e * t = t) (te : t * e = t) (tt : t * t = e)
    (s u : Finset ℕ) :
    supportPoint n e t (s ∆ u) = supportPoint n e t s * supportPoint n e t u := by
  funext i
  simp only [supportPoint, Pi.mul_apply, Finset.mem_symmDiff]
  by_cases hs : i.val ∈ s <;> by_cases hu : i.val ∈ u <;>
    simp [hs, hu, ee, et, te, tt]

private def edge (i j : Fin 4) : Finset (Fin 4) := {i, j}
private def face (i j k : Fin 4) : Finset (Fin 4) := {i, j, k}

private theorem face_triangle {L : Type*} (x : Finset (Fin 4) → L) (i j k : Fin 4)
    (different : [i, j, k].Nodup) :
    x '' (↑((face i j k).powersetCard 2) : Set (Finset (Fin 4))) =
      {x (edge i j), x (edge i k), x (edge j k)} := by
  have pairs (i j k : Fin 4) (h : [i, j, k].Nodup) :
      (face i j k).powersetCard 2 = {edge i j, edge i k, edge j k} := by
    revert i j k
    decide
  rw [pairs i j k different]
  simp

/-- A finite power contains a Pasch of one colour for every finite labelling of its blocks. -/
private theorem monochromaticPasch {L A : Type*} [Mul L] [Finite A] (e t : L)
    (different : t ≠ e) (unit : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) :
    ∃ n : ℕ, ∀ label : Set (Fin n → L) → A,
      ∃ p q a b c d : Fin n → L,
        [(fun _ => e), p, q, a, b, c, d].Nodup ∧
        q * a = b ∧ p * b = c ∧ q * c = d ∧ p * d = a ∧
        label {q, a, b} = label {p, b, c} ∧
        label {q, a, b} = label {q, c, d} ∧
        label {q, a, b} = label {p, d, a} := by
  classical
  obtain ⟨n, ramsey⟩ := finiteRamseyPrefix (A := A) 3 4
  refine ⟨n, ?_⟩
  intro label
  let color (s : Finset ℕ) :=
    label (supportPoint n e t '' (↑(s.powersetCard 2) : Set (Finset ℕ)))
  obtain ⟨core, inRange, size, value, mono⟩ := ramsey color
  let coordinates := (core.equivFinOfCardEq size).symm.toEmbedding.trans (Function.Embedding.subtype _)
  have inCore (i : Fin 4) : coordinates i ∈ core := ((core.equivFinOfCardEq size).symm i).property
  have small (i : Fin 4) : coordinates i < n := Finset.mem_range.mp (inRange (inCore i))
  let x (s : Finset (Fin 4)) := supportPoint n e t (s.map coordinates)
  have injective : Function.Injective x := by
    intro s u equal
    ext i
    have observed := congrFun equal ⟨coordinates i, small i⟩
    change (if coordinates i ∈ s.map coordinates then t else e) =
      (if coordinates i ∈ u.map coordinates then t else e) at observed
    simp only [Finset.mem_map'] at observed
    by_cases hs : i ∈ s <;> by_cases hu : i ∈ u <;>
      simp_all [Ne.symm different]
  have et : e * t = t := unit t
  have te : t * e = t := (comm t e).trans et
  have tt : t * t = e := by simpa only [te] using invol t e
  have xor_mul (s u : Finset (Fin 4)) : x (s ∆ u) = x s * x u := by
    change supportPoint n e t ((s ∆ u).map coordinates) = _
    rw [show (s ∆ u).map coordinates = s.map coordinates ∆ u.map coordinates by
      simpa only [Finset.map_eq_image] using Finset.image_symmDiff s u coordinates.injective]
    exact supportPoint_mul n e t (unit e) et te tt _ _
  have mapColor (s : Finset (Fin 4)) :
      color (s.map coordinates) =
        label (x '' (↑(s.powersetCard 2) : Set (Finset (Fin 4)))) := by
    simp [color, Finset.powersetCard_map, Finset.coe_map, Set.image_image, x]
  have faceColor (i j k : Fin 4) (distinct : [i, j, k].Nodup) :
      label {x (edge i j), x (edge i k), x (edge j k)} = value := by
    have faceSize (i j k : Fin 4) : [i, j, k].Nodup → (face i j k).card = 3 := by
      revert i j k
      decide
    have inside : (face i j k).map coordinates ⊆ core := by
      intro z hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
      exact inCore a
    have h := mono _ inside (by simpa using faceSize i j k distinct)
    rwa [mapColor, face_triangle x i j k distinct] at h
  have first : label {x (edge 2 3), x (edge 0 2), x (edge 0 3)} = value := by
    convert faceColor 0 2 3 (by decide) using 1
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨x (edge 0 1), x (edge 2 3), x (edge 0 2), x (edge 0 3),
    x (edge 1 3), x (edge 1 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have distinct : ([∅, edge 0 1, edge 2 3, edge 0 2, edge 0 3, edge 1 3, edge 1 2] :
        List (Finset (Fin 4))).Nodup := by decide
    have zero : x ∅ = fun _ => e := by
      funext i
      simp [x, supportPoint]
    simpa only [List.map_cons, List.map_nil, zero] using distinct.map injective
  · rw [← xor_mul, show edge 2 3 ∆ edge 0 2 = edge 0 3 by decide]
  · rw [← xor_mul, show edge 0 1 ∆ edge 0 3 = edge 1 3 by decide]
  · rw [← xor_mul, show edge 2 3 ∆ edge 1 3 = edge 1 2 by decide]
  · rw [← xor_mul, show edge 0 1 ∆ edge 1 2 = edge 0 2 by decide]
  · exact first.trans (faceColor 0 1 3 (by decide)).symm
  · refine first.trans ?_
    symm
    convert faceColor 1 2 3 (by decide) using 1
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · refine first.trans ?_
    symm
    convert faceColor 0 1 2 (by decide) using 1
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

private noncomputable def liftedStep {L A : Type*} [Mul L] [AddCommGroup A]
    (e p q : L) (labels : Set L → A) (z : L × A) : L × A :=
  letI := extensionMul e labels
  (p, 0) * ((q, 0) * z)

private noncomputable def starts {L A : Type*} [Mul L] [AddCommGroup A]
    (e p q : L) (labels : Set L → A) : Set (L × A) :=
  {z | (liftedStep e p q labels)^[2] z ≠ z}

theorem improve {L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Nontrivial A]
    (G : SimpleGraph L) (e p q x : L) (labels : Set L → A)
    (unit : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centre : Set.center L = {e})
    (hp : p ≠ e) (hq : q ≠ e) (hpq : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (outside : G.connectedComponentMk x ≠ G.connectedComponentMk e)
    (stationary : (liftedStep e p q labels)^[2] (x, 0) = (x, 0)) :
    ∃ better : Set L → A, (starts e p q labels).ncard < (starts e p q better).ncard := by
  classical
  let g : L → L := fun y => p * (q * y)
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  have oldInv := (extensionSteinerAndCentre e labels unit comm invol twice centre).2.2.1
  obtain ⟨nonzero, different⟩ := exists_ne (0 : A)
  obtain ⟨better, _, _, betterInv, _, support⟩ :=
    extensionNoncommutingCount G e p q unit comm invol twice centre hpq hp hq edges
      (fun _ => nonzero)
  let _ := extensionMul e better
  have newMove {u : L} (hu : G.connectedComponentMk u ≠ G.connectedComponentMk e)
      (a : A) : (u, a) ∈ starts e p q better := by
    have selected : (u, a) ∈
        {z : L × A | (q, 0) * ((p, 0) * z) ≠ (p, 0) * ((q, 0) * z)} := by
      rw [support]
      exact ⟨Or.inr ⟨hu, different⟩, Set.mem_univ _⟩
    exact fun fixed =>
      selected ((squareFixed (betterInv (p, 0)) (betterInv (q, 0)) (u, a)).mpr fixed)
  have inclusion : starts e p q labels ⊆ starts e p q better := by
    rintro ⟨u, a⟩ moves stable
    change (liftedStep e p q better)^[2] (u, a) = (u, a) at stable
    have closes : g^[2] u = u := congrArg Prod.fst stable
    by_cases outside' : G.connectedComponentMk u ≠ G.connectedComponentMk e
    · exact newMove outside' a stable
    · have reach : G.Reachable e u := ConnectedComponent.exact (not_not.mp outside').symm
      have atE (b : A) :
          (liftedStep e p q labels)^[minimalPeriod g e] (e, b) = (e, b + 0) := by
        obtain ⟨period, identity⟩ := identityReturn e p q labels b unit comm invol twice hpq
        rw [pairedLift_eq_mul e labels p q] at identity
        have k : minimalPeriod g e = 2 := period
        rw [k, add_zero]
        exact identity
      have along := returnAlongComponent G e p q labels invol twice edges oldInv reach 0 atE a
      have period := steinerSquarePeriod comm invol hpq closes
      rw [period, add_zero] at along
      exact moves along
  refine ⟨better, Set.ncard_lt_ncard (lt_of_le_not_ge inclusion ?_)⟩
  intro reverse
  exact reverse (newMove outside 0) stationary

private theorem stationaryOnMonochromaticPasch {L A : Type*} [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] (e p q a b c d : L)
    (labels : Set L → A) (distinct : [e, p, q, a, b, c, d].Nodup)
    (hab : q * a = b) (hbc : p * b = c) (hcd : q * c = d) (hda : p * d = a)
    (first : labels {q, a, b} = labels {p, b, c})
    (second : labels {q, a, b} = labels {q, c, d})
    (third : labels {q, a, b} = labels {p, d, a}) :
    (liftedStep e p q labels)^[2] (a, 0) = (a, 0) := by
  let _ := extensionMul e labels
  have increment {u v w : L} (h : u * v = w)
      (nondegenerate : ¬ (u = e ∨ v = e ∨ u = v)) (s : A) :
      (u, (0 : A)) * (v, s) = (w, s + labels {u, v, w}) := by
    change (u * v, 0 + s + factor e labels u v) = _
    rw [zero_add, factor, ite_eq_right nondegenerate]
    change (u * v, s + labels {u, v, u * v}) = _
    rw [h]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have step1 := increment hab (by tauto) 0
  have step2 := increment hbc (by tauto)
    (0 + labels {q, a, b})
  have step3 := increment hcd (by tauto)
    (0 + labels {q, a, b} + labels {p, b, c})
  have step4 := increment hda (by tauto)
    (0 + labels {q, a, b} + labels {p, b, c} + labels {q, c, d})
  change (p, 0) * ((q, 0) * ((p, 0) * ((q, 0) * (a, (0 : A))))) = (a, 0)
  rw [step1, step2, step3, step4, ← first, ← second, ← third]
  have twice : labels {q, a, b} + labels {q, a, b} = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using
      congrArg (fun r : ZMod 2 => r • labels {q, a, b}) two
  simp only [zero_add, twice]

/-- Successful starts at the zero lifts, counted in the normalized extension. -/
noncomputable def switchCount {L A : Type*} [Mul L] [AddCommGroup A]
    (e p q : L) (labels : Set L → A) : ℕ :=
  letI := extensionMul e labels
  ({x : L × A | (q, 0) * ((p, 0) * x) ≠ (p, 0) * ((q, 0) * x)} : Set (L × A)).ncard

theorem switchCount_eq {L A : Type*} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e p q : L) (labels : Set L → A)
    (unit : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centre : Set.center L = {e}) :
    switchCount e p q labels = (starts e p q labels).ncard := by
  let _ := extensionMul e labels
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  have law := (extensionSteinerAndCentre e labels unit comm invol twice centre).2.2.1
  unfold switchCount
  congr 1
  ext x
  exact not_congr (squareFixed (law (p, 0)) (law (q, 0)) x)

/-- Every fixed nontrivial finite binary fibre fails to attain all individual switch
maxima simultaneously on some finite power of a nontrivial centreless Steiner loop. -/
theorem noCommonMaximumInSomePower {L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Nontrivial A]
    (e t : L) (different : t ≠ e) (unit : ∀ x, e * x = x)
    (comm : ∀ x y : L, x * y = y * x) (invol : ∀ x y : L, x * (x * y) = y)
    (centre : Set.center L = {e}) :
    ∃ n : ℕ, 0 < n ∧ ∀ labels : Set (Fin n → L) → A,
      ∃ p q : Fin n → L, p ≠ (fun _ => e) ∧ q ≠ (fun _ => e) ∧ p ≠ q ∧
        ∃ better : Set (Fin n → L) → A,
          switchCount (fun _ => e) p q labels < switchCount (fun _ => e) p q better := by
  obtain ⟨n, monochromatic⟩ := monochromaticPasch (A := A) e t different unit comm invol
  have positive : 0 < n := by
    by_contra! contrary
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero contrary
    obtain ⟨p, q, a, b, c, d, distinct, _⟩ := monochromatic (fun _ => 0)
    have same : (fun _ : Fin 0 => e) = p := funext fun i => Fin.elim0 i
    exact ((List.nodup_cons.mp distinct).1) (by simp [same])
  let identity : Fin n → L := fun _ => e
  have unit' (x : Fin n → L) : identity * x = x := funext fun j => unit (x j)
  have comm' (x y : Fin n → L) : x * y = y * x := funext fun j => comm (x j) (y j)
  have invol' (x y : Fin n → L) : x * (x * y) = y := funext fun j => invol (x j) (y j)
  have centre' : Set.center (Fin n → L) = {identity} := by
    rw [Set.center_pi]
    ext x
    simp only [centre, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_singleton_iff]
    exact funext_iff.symm
  refine ⟨n, positive, ?_⟩
  intro labels
  obtain ⟨p, q, a, b, c, d, distinct, hab, hbc, hcd, hda, first, second, third⟩ :=
    monochromatic labels
  have stopped := stationaryOnMonochromaticPasch identity p q a b c d labels
    distinct hab hbc hcd hda first second third
  change [identity, p, q, a, b, c, d].Nodup at distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have hp : p ≠ identity := Ne.symm (by tauto : identity ≠ p)
  have hq : q ≠ identity := Ne.symm (by tauto : identity ≠ q)
  have hpq : p ≠ q := by tauto
  let M := loopPivotMatchings identity p q unit' comm' invol' hp hq hpq
  have rightUnit (x : Fin n → L) : x * identity = x := (comm' x identity).trans (unit' x)
  have commute : M.first (M.second identity) = M.second (M.first identity) := by
    change p * (q * identity) = q * (p * identity)
    rw [rightUnit, rightUnit, comm']
  have special : (M.graph.connectedComponentMk identity).supp = {identity, p, q, p * q} := by
    have corners := M.component_eq_square commute
    change (M.graph.connectedComponentMk identity).supp =
      {identity, p * identity, q * identity, p * (q * identity)} at corners
    simpa only [rightUnit] using corners
  have outside : M.graph.connectedComponentMk a ≠ M.graph.connectedComponentMk identity := by
    intro same
    have mem := (ConnectedComponent.mem_supp_iff _ _).mpr same
    rw [special] at mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mem
    have apart : a ≠ p * q := by
      intro equation
      have bp : b = p := by rw [← hab, equation, comm' p q, invol']
      exact (by tauto : p ≠ b) bp.symm
    rcases mem with equal | equal | equal | equal
    · exact (by tauto : identity ≠ a) equal.symm
    · exact (by tauto : p ≠ a) equal.symm
    · exact (by tauto : q ≠ a) equal.symm
    · exact apart equal
  obtain ⟨better, greater⟩ := improve M.graph identity p q a labels
    unit' comm' invol' centre' hp hq hpq (fun _ _ => Iff.rfl) outside stopped
  refine ⟨p, q, hp, hq, hpq, better, ?_⟩
  rw [switchCount_eq identity p q labels unit' comm' invol' centre',
    switchCount_eq identity p q better unit' comm' invol' centre']
  exact greater

end D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
