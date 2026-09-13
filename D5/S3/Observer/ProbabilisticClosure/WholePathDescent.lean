/- GID: D5/S3/Observer/ProbabilisticClosure/WholePathDescent
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/WholePathDescent
   mirror-E: none(waiver:universal-pmf-identity)
   anchors: []
   utility: none
   digest: Exact one-step stochastic descent transports the joint law of every
     finite path, not merely independent endpoints or single-time marginals. -/

import D5.S3.Observer.ProbabilisticClosure.StrongLumpabilityDescent

set_option autoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.WholePathDescent

noncomputable section

/-- A complete path with its initial state and exactly n subsequent transitions.
One hidden state is shared between each two successive transitions. -/
def pathLaw {X : Type*} (K : X → PMF X) : Nat → X → PMF (List X)
  | 0, x => PMF.pure [x]
  | n + 1, x => (K x).bind (fun y => (pathLaw K n y).map (List.cons x))

/-- Pushing the entire hidden path forward equals the joint quotient path law.
The hypothesis is the exact one-step descent provided by strong lumpability.
It must hold at every hidden state, not just for a chosen initial distribution. -/
theorem whole_path_descent {X Y : Type*} (q : X → Y)
    (K : X → PMF X) (L : Y → PMF Y)
    (h : ∀ x, (K x).map q = L (q x)) (n : Nat) (x : X) :
    (pathLaw K n x).map (List.map q) = pathLaw L n (q x) := by
  induction n generalizing x with
  | zero => simp [pathLaw, PMF.pure_map]
  | succ n ih =>
    rw [pathLaw, PMF.map_bind]
    calc
      (K x).bind (fun y => ((pathLaw K n y).map (List.cons x)).map (List.map q)) =
          (K x).bind (fun y =>
            ((pathLaw K n y).map (List.map q)).map (List.cons (q x))) := by
        congr 1
        funext y
        rw [PMF.map_comp, PMF.map_comp]
        congr 1
        funext w
        simp
      _ = (K x).bind (fun y => (pathLaw L n (q y)).map (List.cons (q x))) := by
        simp_rw [ih]
      _ = ((K x).map q).bind (fun y =>
          (pathLaw L n y).map (List.cons (q x))) := by
        rw [PMF.bind_map]
        rfl
      _ = pathLaw L (n + 1) (q x) := by rw [h x]; rfl

/-- Mixtures of initial hidden states are allowed without resetting the hidden
fiber between successive times. The equality remains one of full joint laws. -/
theorem initial_distribution_path_descent {X Y : Type*} (q : X → Y)
    (K : X → PMF X) (L : Y → PMF Y)
    (h : ∀ x, (K x).map q = L (q x)) (mu : PMF X) (n : Nat) :
    (mu.bind (pathLaw K n)).map (List.map q) =
      (mu.map q).bind (pathLaw L n) := by
  rw [PMF.map_bind, PMF.bind_map]
  simp_rw [whole_path_descent q K L h]
  rfl

/-- Every statistic of the observed whole path has the transported law. This
includes an intermediate visit, endpoint pair, or an integer-valued path cost. -/
theorem path_statistic_descent {X Y Z : Type*} (q : X → Y)
    (K : X → PMF X) (L : Y → PMF Y)
    (h : ∀ x, (K x).map q = L (q x))
    (n : Nat) (x : X) (F : List Y → Z) :
    (pathLaw K n x).map (F ∘ List.map q) = (pathLaw L n (q x)).map F := by
  rw [← PMF.map_comp, whole_path_descent q K L h]

#print axioms whole_path_descent
#print axioms initial_distribution_path_descent
#print axioms path_statistic_descent

end
end D5.S3.Observer.ProbabilisticClosure.WholePathDescent
