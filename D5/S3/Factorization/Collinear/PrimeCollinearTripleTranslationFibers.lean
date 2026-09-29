/- GID: D5/S3/Factorization/Collinear/PrimeCollinearTripleTranslationFibers
   generality: I
   mirror-B: D5/B/S3/Factorization/Collinear/PrimeCollinearTripleTranslationFibers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prime translation orbits are exactly slope and translated-abscissa fibers. -/

import D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace D5.S3.Factorization.Collinear.PrimeCollinearTripleTranslationFibers

open scoped Pointwise
open D5.S3.Factorization.CollinearTripleTranslationOrbits
open D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus

def PrimeTripleParameters (p : ℕ) :=
  ({a : ZMod p // a ≠ 0} × ZMod p) × {X : Finset (ZMod p) // X.card = 3}

private def graph (a b : ZMod p) (X : Finset (ZMod p)) : Finset (Point p) :=
  X.image (fun x => (x, a * x + b))

private theorem graph_fst (a b : ZMod p) (X : Finset (ZMod p)) :
    (graph a b X).image Prod.fst = X := by
  simp [graph, Finset.image_image, Function.comp_def]

private theorem graph_card (a b : ZMod p) (X : Finset (ZMod p)) :
    (graph a b X).card = X.card := by
  apply Finset.card_image_of_injOn
  intro x _ y _ h
  exact congrArg Prod.fst h

private theorem graph_valid (p : ℕ) (hp : p.Prime)
    (a b : ZMod p) (ha : a ≠ 0) (X : Finset (ZMod p)) (hX : X.card = 3) :
    IsCollinearTriple (graph a b X) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨(graph_card a b X).trans hX, ?_, ?_, ?_⟩
  · intro z hz z' hz' h
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
    exact congrArg (fun x : ZMod p => (x, a * x + b)) h
  · intro z hz z' hz' h
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
    have hxy : x = y := (mul_left_cancel₀ ha) (add_right_cancel h)
    exact congrArg (fun x : ZMod p => (x, a * x + b)) hxy
  · intro z hz z' hz' z'' hz''
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hz'' with ⟨w, hw, rfl⟩
    dsimp
    ring

private noncomputable def graphTriple (p : ℕ) (hp : p.Prime)
    (q : PrimeTripleParameters p) : Triple p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨graph q.1.1.val q.1.2 q.2.val,
    graph_valid p hp q.1.1.val q.1.2 q.1.1.property q.2.val q.2.property⟩

private theorem graphTriple_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (graphTriple p hp) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro q r hqr
  have hgraph : graph q.1.1.val q.1.2 q.2.val =
      graph r.1.1.val r.1.2 r.2.val := congrArg Subtype.val hqr
  have hX : q.2.val = r.2.val := by
    calc
      q.2.val = (graph q.1.1.val q.1.2 q.2.val).image Prod.fst :=
        (graph_fst _ _ _).symm
      _ = (graph r.1.1.val r.1.2 r.2.val).image Prod.fst := congrArg _ hgraph
      _ = r.2.val := graph_fst _ _ _
  obtain ⟨x, y, z, hxy, hxz, hyz, hXYZ⟩ := Finset.card_eq_three.mp q.2.property
  have hx : x ∈ q.2.val := by rw [hXYZ]; simp
  have hy : y ∈ q.2.val := by rw [hXYZ]; simp [hxy.symm]
  have hpoint (u : ZMod p) (hu : u ∈ q.2.val) :
      q.1.1.val * u + q.1.2 = r.1.1.val * u + r.1.2 := by
    have hmem : (u, q.1.1.val * u + q.1.2) ∈
        graph r.1.1.val r.1.2 r.2.val := by
      have hmemq : (u, q.1.1.val * u + q.1.2) ∈
          graph q.1.1.val q.1.2 q.2.val :=
        Finset.mem_image.mpr ⟨u, hu, rfl⟩
      rw [hgraph] at hmemq
      exact hmemq
    rcases Finset.mem_image.mp hmem with ⟨v, hv, heq⟩
    have huv : v = u := congrArg Prod.fst heq
    simpa [huv] using (congrArg Prod.snd heq).symm
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hmul : (q.1.1.val - r.1.1.val) * (x - y) = 0 := by
    linear_combination hpoint x hx - hpoint y hy
  have ha : q.1.1.val = r.1.1.val := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hmul).resolve_right hxy'
  have hb : q.1.2 = r.1.2 := by
    linear_combination hpoint x hx - ha * x
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext ha
    · exact hb
  · exact Subtype.ext hX

private theorem parameter_card (p : ℕ) (hp : p.Prime) :
    Nat.card (PrimeTripleParameters p) =
      p * (p - 1) * Nat.choose p 3 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hnonzero : Nat.card {a : ZMod p // a ≠ 0} = p - 1 := by
    rw [Nat.card_eq_fintype_card]
    have h : Fintype.card {a : ZMod p // a ≠ 0} =
        (Finset.univ.erase (0 : ZMod p)).card :=
      Fintype.card_of_subtype _ (by intro x; simp)
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
    simp
  have hchoose : Nat.card {X : Finset (ZMod p) // X.card = 3} = Nat.choose p 3 := by
    rw [Nat.card_eq_fintype_card]
    have h : Fintype.card {X : Finset (ZMod p) // X.card = 3} =
        (Finset.univ.powersetCard 3 : Finset (Finset (ZMod p))).card :=
      Fintype.card_of_subtype _ (by intro X; simp)
    rw [h, Finset.card_powersetCard]
    simp
  have hK : Nat.card (ZMod p) = p := by simp
  simp only [PrimeTripleParameters, Nat.card_prod, hnonzero, hchoose, hK]
  rw [Nat.mul_comm (p - 1) p]

private theorem graphTriple_surjective (p : ℕ) (hp : p.Prime) :
    Function.Surjective (graphTriple p hp) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Finite (PrimeTripleParameters p) := by
    unfold PrimeTripleParameters
    infer_instance
  letI : Fintype (PrimeTripleParameters p) := Fintype.ofFinite _
  letI : Fintype (Triple p) := Fintype.ofFinite _
  have hcard : Fintype.card (PrimeTripleParameters p) = Fintype.card (Triple p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      parameter_card p hp, card_triples_prime p hp]
  exact ((Fintype.bijective_iff_injective_and_card (graphTriple p hp)).mpr
    ⟨graphTriple_injective p hp, hcard⟩).2

noncomputable def parametersOfTriple (p : ℕ) (hp : p.Prime) (s : Triple p) :
    PrimeTripleParameters p :=
  Classical.choose (graphTriple_surjective p hp s)

private theorem graphTriple_parametersOfTriple (p : ℕ) (hp : p.Prime) (s : Triple p) :
    graphTriple p hp (parametersOfTriple p hp s) = s :=
  Classical.choose_spec (graphTriple_surjective p hp s)

private theorem graph_translate (p : ℕ) (hp : p.Prime)
    (q : PrimeTripleParameters p) (h k : ZMod p) :
    (h, k) +ᵥ graphTriple p hp q =
      graphTriple p hp (((q.1.1, q.1.2 + k - q.1.1.val * h),
        ⟨q.2.val.image (h + ·), by
          rw [Finset.card_image_of_injOn]
          · exact q.2.property
          · intro x _ y _ hxy
            exact add_left_cancel hxy⟩)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  change (h, k) +ᵥ graph q.1.1.val q.1.2 q.2.val =
    graph q.1.1.val (q.1.2 + k - q.1.1.val * h) (q.2.val.image (h + ·))
  rw [Finset.vadd_finset_def]
  ext z
  simp only [graph, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨h + x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · apply Prod.ext
      · rfl
      · dsimp
        ring
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(x, q.1.1.val * x + q.1.2), ⟨x, hx, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp
      ring

/-- Prime collinear triples have translation fibers exactly indexed by slope and
translated first-coordinate set; the intercept is removed by a vertical shift. -/
theorem translation_orbit_iff (p : ℕ) (hp : p.Prime) (s t : Triple p) :
    s ∈ AddAction.orbit (Point p) t ↔
      (parametersOfTriple p hp s).1.1.val =
          (parametersOfTriple p hp t).1.1.val ∧
        ∃ h : ZMod p,
          (parametersOfTriple p hp s).2.val =
            (parametersOfTriple p hp t).2.val.image (h + ·) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro hs
    rcases AddAction.mem_orbit_iff.mp hs with ⟨g, rfl⟩
    let q := parametersOfTriple p hp t
    have hq : graphTriple p hp q = t := graphTriple_parametersOfTriple p hp t
    let q' : PrimeTripleParameters p := ((q.1.1, q.1.2 + g.2 - q.1.1.val * g.1),
      ⟨q.2.val.image (g.1 + ·), by
        rw [Finset.card_image_of_injOn]
        · exact q.2.property
        · intro x _ y _ hxy
          exact add_left_cancel hxy⟩)
    have htranslate : g +ᵥ t = graphTriple p hp q' := by
      rw [← hq]
      exact graph_translate p hp q g.1 g.2
    have hq'param : parametersOfTriple p hp (g +ᵥ t) = q' := by
      apply (graphTriple_injective p hp)
      rw [graphTriple_parametersOfTriple, htranslate]
    rw [hq'param]
    exact ⟨rfl, g.1, rfl⟩
  · rintro ⟨ha, ⟨h, hX⟩⟩
    let q := parametersOfTriple p hp t
    let q' := parametersOfTriple p hp s
    let k := q'.1.2 - q.1.2 + q.1.1.val * h
    have hq : graphTriple p hp q = t := graphTriple_parametersOfTriple p hp t
    have hq' : graphTriple p hp q' = s := graphTriple_parametersOfTriple p hp s
    have hparam : q' =
        ((q.1.1, q.1.2 + k - q.1.1.val * h),
          ⟨q.2.val.image (h + ·), by
            rw [← hX]
            exact q'.2.property⟩) := by
      apply Prod.ext
      · apply Prod.ext
        · exact Subtype.ext ha
        · dsimp [k]
          ring
      · exact Subtype.ext hX
    apply AddAction.mem_orbit_iff.mpr
    refine ⟨(h, k), ?_⟩
    calc
      (h, k) +ᵥ t = (h, k) +ᵥ graphTriple p hp q := congrArg _ hq.symm
      _ = graphTriple p hp
          ((q.1.1, q.1.2 + k - q.1.1.val * h),
            ⟨q.2.val.image (h + ·), by rw [← hX]; exact q'.2.property⟩) :=
              graph_translate p hp q h k
      _ = s := by rw [← hparam, hq']

#print axioms translation_orbit_iff

end D5.S3.Factorization.Collinear.PrimeCollinearTripleTranslationFibers
