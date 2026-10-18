/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusSharpness
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual triangle-with-leaf bond law approaches determinant ratio two. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

/-! Actual independent bond laws and sharpness on a one-cycle source graph. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open SimpleGraph
open ThreeTerminalBond
open scoped BigOperators

set_option backward.isDefEq.respectTransparency.types false

/-- Simple cycles are identified by their undirected edge sets. Distinct cycles
of a cactus share at most one vertex. -/
def IsCactus {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
    p.edges.toFinset ≠ q.edges.toFinset →
    (p.support.toFinset ∩ q.support.toFinset).card ≤ 1

/-- Vertices are a=0,b=1,c=2,d=3; edges are db,bc,dc,ad. -/
def pendantEnds : Fin 4 → Fin 4 × Fin 4 := ![(3,1),(1,2),(3,2),(0,3)]

private lemma pendant_partition (ω : Fin 4 → Bool) :
    partition pendantEnds 0 1 2 ω =
      if ω 3 && (ω 0 || (ω 2 && ω 1)) then
        (if ω 1 || (ω 0 && ω 2) then .all else .ab)
      else if ω 1 || (ω 0 && ω 2) then .bc
      else if ω 3 && (ω 2 || (ω 0 && ω 1)) then .ac else .separate := by
  revert ω
  decide +kernel

private lemma cube_four : (Finset.univ : Finset (Fin 4 → Bool)) =
    {![false,false,false,false], ![false,false,false,true],
     ![false,false,true,false], ![false,false,true,true],
     ![false,true,false,false], ![false,true,false,true],
     ![false,true,true,false], ![false,true,true,true],
     ![true,false,false,false], ![true,false,false,true],
     ![true,false,true,false], ![true,false,true,true],
     ![true,true,false,false], ![true,true,false,true],
     ![true,true,true,false], ![true,true,true,true]} := by decide

/-- All five probabilities are computed from the sixteen actual open graphs. -/
theorem pendant_law (u v s A : ℝ) :
    law pendantEnds 0 1 2 ![u,v,s,A] = fun mode => match mode with
      | .separate => (1-A)*(1-v)*(1-u*s)+A*(1-u)*(1-v)*(1-s)
      | .ab => A*u*(1-v)*(1-s)
      | .bc => (1-A)*(v+u*s-v*u*s)+A*v*(1-u)*(1-s)
      | .all => A*(u*v+u*s+v*s-2*u*v*s)
      | .ac => A*s*(1-u)*(1-v) := by
  funext mode
  unfold law
  rw [cube_four]
  simp only [pendant_partition]
  cases mode <;> norm_num [weight,Fin.prod_univ_succ] <;> ring

/-- The determinant retains the triangle contribution and the open pendant arm. -/
theorem pendant_determinant (u v s A : ℝ) :
    delta (law pendantEnds 0 1 2 ![u,v,s,A]) =
      law pendantEnds 0 1 2 ![u,v,s,A] .ac *
        ((1-s)*(u+v-u*v)+(1-A)*(u*v+u*s+v*s-2*u*v*s)) := by
  rw [pendant_law]
  simp only [delta]
  ring

/-- The constant-two bound for every independent rate on the triangle with a leaf. -/
theorem pendant_bound (u v s A : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) (hA : A ∈ Set.Icc 0 1) :
    0 ≤ delta (law pendantEnds 0 1 2 ![u,v,s,A]) ∧
    delta (law pendantEnds 0 1 2 ![u,v,s,A]) ≤
      2*law pendantEnds 0 1 2 ![u,v,s,A] .ac := by
  have hu0 := hu.1
  have hv0 := hv.1
  have hs0 := hs.1
  let K := u*v+u*s+v*s-2*u*v*s
  let L := (1-s)*(u+v-u*v)
  have hu' : 0 ≤ 1-u := sub_nonneg.mpr hu.2
  have hv' : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  have hs' : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hK : 0 ≤ K := by
    calc 0 ≤ u*v*(1-s)+u*s*(1-v)+v*s*(1-u)+u*v*s := by positivity
         _ = K := by dsimp [K]; ring
  have hL : 0 ≤ L := by
    apply mul_nonneg hs'
    nlinarith [mul_nonneg hu' hv.1]
  have hR0 : 0 ≤ L+(1-A)*K :=
    add_nonneg hL (mul_nonneg (sub_nonneg.mpr hA.2) hK)
  have hR2 : L+(1-A)*K ≤ 2 := by
    have hEq : L+(1-A)*K = u+v-s*u*v-A*K := by dsimp [L,K]; ring
    rw [hEq]
    have hprod : 0 ≤ s*u*v := mul_nonneg (mul_nonneg hs.1 hu.1) hv.1
    have hAK : 0 ≤ A*K := mul_nonneg hA.1 hK
    linarith [hu.2,hv.2]
  have hZ : 0 ≤ law pendantEnds 0 1 2 ![u,v,s,A] .ac := by
    rw [pendant_law]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA.1 hs.1) hu') hv'
  rw [pendant_determinant]
  exact ⟨mul_nonneg hZ hR0, by nlinarith [mul_nonneg hZ (sub_nonneg.mpr hR2)]⟩

/-- The claimed exceptional mass and determinant numerator of the sharp family. -/
theorem pendant_sharp_formula (t : ℝ) :
    law pendantEnds 0 1 2 ![1-t,1-t,t,t] .ac = t^4 ∧
    delta (law pendantEnds 0 1 2 ![1-t,1-t,t,t]) =
      t^4*(2-4*t+4*t^2-4*t^3+2*t^4) := by
  rw [pendant_law]
  simp only [delta]
  constructor <;> ring

private lemma pendant_cycle_edges {u : Fin 4}
    (p : (openGraph pendantEnds (fun _ => true)).Walk u u) (hp : p.IsCycle) :
    p.edges.toFinset = {s(1,2),s(1,3),s(2,3)} := by
  let H := openGraph pendantEnds (fun _ => true)
  letI : DecidableRel H.Adj := fun x y =>
    inferInstanceAs (Decidable (x ≠ y ∧
      ((∃ e : Fin 4, true = true ∧ pendantEnds e = (x,y)) ∨
       (∃ e : Fin 4, true = true ∧ pendantEnds e = (y,x)))))
  have hb : H.IsBridge s(0,3) := by
    rw [isBridge_iff]
    decide
  have hnot : s(0,3) ∉ p.edges := hb.notMem_edges_of_isCycle hp
  have hEdges : ∀ e ∈ p.edges, e ∈ ({s(1,2),s(1,3),s(2,3)} : Finset (Sym2 (Fin 4))) := by
    intro e he
    have hh := p.edges_subset_edgeSet he
    have hfull : ∀ e : Sym2 (Fin 4), e ∈ H.edgeSet →
        e = s(0,3) ∨ e ∈ ({s(1,2),s(1,3),s(2,3)} : Finset (Sym2 (Fin 4))) := by
      decide
    exact (hfull e hh).resolve_left (fun h => hnot (h ▸ he))
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    exact hEdges e (List.mem_toFinset.mp he)
  · have hlen : 3 ≤ p.length := hp.three_le_length
    have hcard : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup,Walk.length_edges]
    norm_num
    omega

/-- The sharp family has one simple cycle, so it satisfies the cactus definition. -/
theorem pendant_cactus : IsCactus (openGraph pendantEnds (fun _ => true)) := by
  intro u v p q hp hq hne
  exact (hne ((pendant_cycle_edges p hp).trans (pendant_cycle_edges q hq).symm)).elim

private lemma pendant_connected : (openGraph pendantEnds (fun _ => true)).Connected := by
  constructor
  intro u v
  have h : ∀ u v : Fin 4, connected pendantEnds (fun _ => true) u v = true := by
    decide +kernel
  simpa only [connected,decide_eq_true_eq] using h u v

/-- Every constant below two fails on a fixed four-vertex connected cactus with
all rates strictly inside the probability interval. -/
theorem pendant_sharpness (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : Fin 4 → ℝ,
      (openGraph pendantEnds (fun _ => true)).Connected ∧
      IsCactus (openGraph pendantEnds (fun _ => true)) ∧
      (∀ e, 0 < θ e ∧ θ e < 1) ∧
      0 < law pendantEnds 0 1 2 θ .ac ∧
      (2-ε)*law pendantEnds 0 1 2 θ .ac < delta (law pendantEnds 0 1 2 θ) := by
  let t := min (ε/8) (1/4)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hte : t ≤ ε/8 := min_le_left _ _
  have hθ : ∀ e : Fin 4, 0 < (![1-t,1-t,t,t] : Fin 4 → ℝ) e ∧
      (![1-t,1-t,t,t] : Fin 4 → ℝ) e < 1 := by
    intro e
    fin_cases e <;> simp <;> constructor <;> linarith
  obtain ⟨hZ,hD⟩ := pendant_sharp_formula t
  refine ⟨![1-t,1-t,t,t],pendant_connected,pendant_cactus,hθ,?_,?_⟩
  · rw [hZ]
    positivity
  · rw [hZ,hD]
    have hh : 0 ≤ t^2*(1-t) := mul_nonneg (sq_nonneg _) (by linarith)
    have h4 : 0 ≤ t^4 := pow_nonneg ht.le _
    have hcoef : 2-ε < 2-4*t+4*t^2-4*t^3+2*t^4 := by nlinarith
    calc (2-ε)*t^4 < (2-4*t+4*t^2-4*t^3+2*t^4)*t^4 :=
           mul_lt_mul_of_pos_right hcoef (pow_pos ht 4)
         _ = t^4*(2-4*t+4*t^2-4*t^3+2*t^4) := mul_comm _ _

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_determinant
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_bound
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_law
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_sharp_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_sharp_formula
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_cactus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_cactus
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness.pendant_sharpness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_sharpness

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
