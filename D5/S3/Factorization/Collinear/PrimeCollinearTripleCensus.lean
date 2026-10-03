/- GID: D5/S3/Factorization/Collinear/PrimeCollinearTripleCensus
   generality: I
   mirror-B: D5/B/S3/Factorization/Collinear/PrimeCollinearTripleCensus
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prime triples correspond to nonzero-slope lines and three abscissae. -/

import D5.S3.Factorization.CollinearTripleTranslationOrbits
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus

open D5.S3.Factorization.CollinearTripleTranslationOrbits

/-- The exact count of unordered admissible collinear triples over a prime residue field. -/
theorem card_triples_prime (p : ℕ) (hp : p.Prime) :
    Nat.card (Triple p) = p * (p - 1) * Nat.choose p 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let K := ZMod p
  let graph (a b : K) (X : Finset K) : Finset (Point p) :=
    X.image (fun x => (x, a * x + b))
  have graph_fst (a b : K) (X : Finset K) :
      (graph a b X).image Prod.fst = X := by
    simp [graph, Finset.image_image, Function.comp_def]
  have graph_card (a b : K) (X : Finset K) : (graph a b X).card = X.card := by
    apply Finset.card_image_of_injOn
    intro x _ y _ h
    exact congrArg Prod.fst h
  have graph_valid (a b : K) (ha : a ≠ 0) (X : Finset K) (hX : X.card = 3) :
      IsCollinearTriple (graph a b X) := by
    refine ⟨(graph_card a b X).trans hX, ?_, ?_, ?_⟩
    · intro z hz z' hz' h
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
      exact congrArg (fun x : K => (x, a * x + b)) h
    · intro z hz z' hz' h
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
      have hxy : x = y := (mul_left_cancel₀ ha) (add_right_cancel h)
      exact congrArg (fun x : K => (x, a * x + b)) hxy
    · intro z hz z' hz' z'' hz''
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hz' with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hz'' with ⟨w, hw, rfl⟩
      dsimp
      ring
  have line_exists_unique (s : Triple p) :
      ∃! ab : K × K,
        ab.1 ≠ 0 ∧ ∀ z ∈ s.val, z.2 = ab.1 * z.1 + ab.2 := by
    obtain ⟨u, v, w, huv, huw, hvw, hs⟩ := Finset.card_eq_three.mp s.property.1
    have hu : u ∈ s.val := by rw [hs]; simp
    have hv : v ∈ s.val := by rw [hs]; simp [huv.symm]
    have huxv : u.1 ≠ v.1 := by
      intro h
      exact huv (s.property.2.1 hu hv h)
    have hdy : v.2 - u.2 ≠ 0 := by
      intro h
      exact huv (s.property.2.2.1 hu hv (sub_eq_zero.mp h).symm)
    have hdx : v.1 - u.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm huxv)
    let a : K := (v.2 - u.2) / (v.1 - u.1)
    let b : K := u.2 - a * u.1
    have ha : a ≠ 0 := div_ne_zero hdy hdx
    have hrel : v.2 - u.2 = a * (v.1 - u.1) := by
      dsimp [a]
      field_simp
    have hline (z : Point p) (hz : z ∈ s.val) : z.2 = a * z.1 + b := by
      have hd := s.property.2.2.2 u hu v hv z hz
      have hzrel : z.2 - u.2 = a * (z.1 - u.1) := by
        apply mul_left_cancel₀ hdx
        calc
          (v.1 - u.1) * (z.2 - u.2) = (z.1 - u.1) * (v.2 - u.2) := hd
          _ = (v.1 - u.1) * (a * (z.1 - u.1)) := by rw [hrel]; ring
      dsimp [b]
      linear_combination hzrel
    refine ⟨(a, b), ⟨ha, hline⟩, ?_⟩
    intro ab hab
    have hu' := hab.2 u hu
    have hv' := hab.2 v hv
    have hrel' : v.2 - u.2 = ab.1 * (v.1 - u.1) := by
      linear_combination hv' - hu'
    have heqa : ab.1 = a := by
      apply mul_right_cancel₀ hdx
      exact hrel'.symm.trans hrel
    have heqb : ab.2 = b := by
      rw [heqa] at hu'
      calc
        ab.2 = u.2 - a * u.1 := by linear_combination -hu'
        _ = b := rfl
    exact Prod.ext heqa heqb
  let line : Triple p → K × K := fun s => Classical.choose (line_exists_unique s)
  have line_spec (s : Triple p) :
      (line s).1 ≠ 0 ∧ ∀ z ∈ s.val, z.2 = (line s).1 * z.1 + (line s).2 :=
    (Classical.choose_spec (line_exists_unique s)).1
  have line_unique (s : Triple p) (ab : K × K)
      (h : ab.1 ≠ 0 ∧ ∀ z ∈ s.val, z.2 = ab.1 * z.1 + ab.2) :
      ab = line s := (Classical.choose_spec (line_exists_unique s)).2 ab h
  have graph_eq (s : Triple p) :
      graph (line s).1 (line s).2 (s.val.image Prod.fst) = s.val := by
    change (s.val.image Prod.fst).image
      (fun x => (x, (line s).1 * x + (line s).2)) = s.val
    rw [Finset.image_image]
    calc
      s.val.image (fun z => (z.1, (line s).1 * z.1 + (line s).2)) =
          s.val.image id := by
        apply Finset.image_congr
        intro z hz
        exact Prod.ext rfl ((line_spec s).2 z hz).symm
      _ = s.val := Finset.image_id
  let Data := ({a : K // a ≠ 0} × K) × {X : Finset K // X.card = 3}
  let encode : Triple p → Data := fun s =>
    ((⟨(line s).1, (line_spec s).1⟩, (line s).2),
      ⟨s.val.image Prod.fst, (Finset.card_image_of_injOn s.property.2.1).trans s.property.1⟩)
  have encode_injective : Function.Injective encode := by
    intro s t h
    have ha : (line s).1 = (line t).1 := congrArg (fun d : Data => d.1.1.val) h
    have hb : (line s).2 = (line t).2 := congrArg (fun d : Data => d.1.2) h
    have hX : s.val.image Prod.fst = t.val.image Prod.fst :=
      congrArg (fun d : Data => d.2.val) h
    apply Subtype.ext
    calc
      s.val = graph (line s).1 (line s).2 (s.val.image Prod.fst) := (graph_eq s).symm
      _ = graph (line t).1 (line t).2 (t.val.image Prod.fst) := by rw [ha, hb, hX]
      _ = t.val := graph_eq t
  have encode_surjective : Function.Surjective encode := by
    intro d
    let s : Triple p := ⟨graph d.1.1.val d.1.2 d.2.val,
      graph_valid d.1.1.val d.1.2 d.1.1.property d.2.val d.2.property⟩
    have hline : (d.1.1.val, d.1.2) = line s := by
      apply line_unique
      constructor
      · exact d.1.1.property
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        rfl
    refine ⟨s, ?_⟩
    refine Prod.ext ?_ ?_
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hline.symm
      · change (line s).2 = d.1.2
        exact congrArg Prod.snd hline.symm
    · apply Subtype.ext
      exact graph_fst d.1.1.val d.1.2 d.2.val
  have hcard : Nat.card (Triple p) = Nat.card Data :=
    Nat.card_congr (Equiv.ofBijective encode ⟨encode_injective, encode_surjective⟩)
  have hnonzero : Nat.card {a : K // a ≠ 0} = p - 1 := by
    rw [Nat.card_eq_fintype_card]
    have h : Fintype.card {a : K // a ≠ 0} =
        (Finset.univ.erase (0 : K)).card :=
      Fintype.card_of_subtype _ (by intro x; simp)
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ (0 : K))]
    simp [K]
  have hchoose : Nat.card {X : Finset K // X.card = 3} = Nat.choose p 3 := by
    rw [Nat.card_eq_fintype_card]
    have h : Fintype.card {X : Finset K // X.card = 3} =
        (Finset.univ.powersetCard 3 : Finset (Finset K)).card :=
      Fintype.card_of_subtype _ (by intro X; simp)
    rw [h, Finset.card_powersetCard]
    simp [K]
  have hK : Nat.card K = p := by simp [K]
  rw [hcard]
  simp only [Data, Nat.card_prod, hnonzero, hchoose, hK]
  rw [Nat.mul_comm (p - 1) p]

#print axioms card_triples_prime

end D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
