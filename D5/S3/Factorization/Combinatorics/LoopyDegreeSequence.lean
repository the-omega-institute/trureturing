/- GID: D5/S3/Factorization/Combinatorics/LoopyDegreeSequence
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/LoopyDegreeSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary Loopy equality recovers the complete concrete degree multiset. -/
import D5.S3.Factorization.Combinatorics.LoopyEvaluator
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import D5.S1.Recurrence.Witt.PrimitiveEulerLedger
import Mathlib.RingTheory.PowerSeries.Expand
set_option autoImplicit false
namespace D5.S3.Factorization.Combinatorics.LoopyDegreeSequence
noncomputable section
open scoped BigOperators
open PowerSeries
/-- Contribution of one stored endpoint pair to the actual graph-theoretic degree. -/
def incidence (e : Edge) (v : Nat) : Nat :=
  (if e.1 = v then 1 else 0) + if e.2 = v then 1 else 0
/-- Degree contributed by the pending edge occurrences. -/
def pendingDegree : List Edge → Nat → Nat
  | [], _ => 0
  | e :: E, v => incidence e v + pendingDegree E v
/-- Actual degree, counting each accumulated or pending loop twice. -/
def degree (E : List Edge) (ell : Nat → Nat) (v : Nat) : Nat :=
  2 * ell v + pendingDegree E v
/-- The actual degree multiset, including isolated vertices and multiplicity. -/
def degreeMultiset (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) : Multiset Nat :=
  V.1.map (degree E ell)
/-- The geometric sum `1 + t + ... + t^(h-1)`. -/
def geometricSum (h : Nat) : Polynomial Int :=
  ∑ i ∈ Finset.range h, Polynomial.X ^ i
/-- Degree-product specialization of the Loopy variables. -/
def degreeSpecialization : LoopyPolynomial →+* Polynomial Int :=
  MvPolynomial.eval₂Hom (RingHom.id _) fun r => geometricSum (2 * r + 1)
/- The substitution x_r = [2r+1] is proved in this module. The primary source is
https://arxiv.org/html/2609.07728v1, exact target Problem 11.4, with public
preregistration https://github.com/the-omega-institute/trureturing/issues/8149;
source section 6.5 concerns refined-degree problem context, not this claim. -/
/-- The ordinary U-specialization `t = 1`, `x_r = z`. -/
def orderSpecialization : LoopyPolynomial →+* Polynomial Int :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (Polynomial.evalRingHom 1)) fun _ => Polynomial.X

/-- The ordinary Loopy polynomial determines the complete degree multiset for every
finite labelled undirected multigraph, including loops, parallel edges, isolates,
disconnected graphs, and the empty graph. -/
theorem loopy_determines_degree_multiset
    (V W : Finset Nat) (E F : List Edge) (ell eta : Nat → Nat)
    (hG : Valid V E ell) (hH : Valid W F eta)
    (hL : loopy V E ell = loopy W F eta) :
    degreeMultiset V E ell = degreeMultiset W F eta := by
  have localFacts :
      (∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat),
          Valid V E ell →
            degreeSpecialization (loopy V E ell) =
              ∏ v ∈ V, geometricSum (degree E ell v + 1)) ∧
      (∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat),
          (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) →
            Polynomial.IsMonicOfDegree (orderSpecialization (loopy V E ell)) V.card) := by
    constructor
    · intro V E ell hvalid
      classical
      classical
      have geometric_identity (p q : Nat) :
          geometricSum (p + 1) * geometricSum (q + 1) =
            Polynomial.X * geometricSum p * geometricSum q + geometricSum (p + q + 1) := by
        apply mul_right_cancel₀ (b := (1 - Polynomial.X) ^ 2)
          (pow_ne_zero 2 (sub_ne_zero.mpr (by
            intro h
            have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 0) h
            simpa using hcoeff)))
        have geometric_mul (r : Nat) :
            geometricSum r * (1 - Polynomial.X) = 1 - Polynomial.X ^ r := by
          exact geom_sum_mul_neg Polynomial.X r
        calc
          (geometricSum (p + 1) * geometricSum (q + 1)) *
              (1 - Polynomial.X) ^ 2 =
              (geometricSum (p + 1) * (1 - Polynomial.X)) *
                (geometricSum (q + 1) * (1 - Polynomial.X)) := by ring
          _ = (1 - Polynomial.X ^ (p + 1)) * (1 - Polynomial.X ^ (q + 1)) := by
            rw [geometric_mul, geometric_mul]
          _ = Polynomial.X * (geometricSum p * (1 - Polynomial.X)) *
                (geometricSum q * (1 - Polynomial.X)) +
              (geometricSum (p + q + 1) * (1 - Polynomial.X)) *
                (1 - Polynomial.X) := by
            rw [geometric_mul, geometric_mul, geometric_mul]
            ring
          _ = (Polynomial.X * geometricSum p * geometricSum q +
              geometricSum (p + q + 1)) * (1 - Polynomial.X) ^ 2 := by ring
      have core : ∀ n : Nat, ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat),
          E.length = n → Valid V E ell →
          degreeSpecialization (loopyAux V E ell) =
            ∏ v ∈ V, geometricSum (degree E ell v + 1) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            intro V E ell hlen hvalid
            cases E with
            | nil =>
                simp [loopyAux, degreeSpecialization, degree, pendingDegree, geometricSum]
            | cons e E =>
                rcases e with ⟨a, b⟩
                have hhead := hvalid.1 (a, b) (by simp)
                have haV : a ∈ V := hhead.1
                have hbV : b ∈ V := hhead.2
                have hlt : E.length < n := by
                  have hsucc : E.length + 1 = n := by simpa using hlen
                  omega
                have htail : Valid V E ell := by
                  refine ⟨?_, hvalid.2⟩
                  intro e he
                  exact hvalid.1 e (by simp [he])
                by_cases hab : a = b
                · subst b
                  have hadd : Valid V E (addLoop ell a) := by
                    refine ⟨htail.1, ?_⟩
                    intro v hv
                    have hva : v ≠ a := fun h => hv (h ▸ haV)
                    simp [addLoop, hva, hvalid.2 v hv]
                  have hdeg (v : Nat) :
                      degree E (addLoop ell a) v = degree ((a, a) :: E) ell v := by
                    by_cases hva : v = a
                    · subst v
                      simp [degree, pendingDegree, incidence, addLoop]
                      omega
                    · simp [degree, pendingDegree, incidence, addLoop, hva, Ne.symm hva]
                  simp only [loopyAux]
                  simp
                  rw [ih E.length hlt V E (addLoop ell a) rfl hadd]
                  apply Finset.prod_congr rfl
                  intro v hv
                  rw [hdeg]
                · have hcontract : Valid (V.erase b) (E.map (contractEdge a b))
                      (contractLoops ell a b) := by
                    constructor
                    · intro e he
                      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
                      have hfV := htail.1 f hf
                      have map_mem (x : Nat) (hx : x ∈ V) :
                          contractVertex a b x ∈ V.erase b := by
                        by_cases hxb : x = b
                        · subst x
                          simp [contractVertex, haV, hab]
                        · simp [contractVertex, hxb, hx, hab]
                      exact And.intro (map_mem f.1 hfV.1) (map_mem f.2 hfV.2)
                    · intro v hv
                      have hva : v ≠ a := by
                        intro h
                        subst v
                        exact hv (by simp [haV, hab])
                      by_cases hvb : v = b
                      · subst v
                        simp [contractLoops, hva]
                      · have hvV : v ∉ V := fun h => hv (by simp [h, hvb])
                        simp [contractLoops, hva, hvb, hvalid.2 v hvV]
                  have hsingleA (f : Edge) :
                      incidence (contractEdge a b f) a = incidence f a + incidence f b := by
                    rcases f with ⟨x, y⟩
                    by_cases hxb : x = b <;> by_cases hyb : y = b <;>
                      simp [incidence, contractEdge, contractVertex, hxb, hyb, hab,
                        Ne.symm hab] <;> omega
                  have hincA (L : List Edge) :
                      pendingDegree (L.map (contractEdge a b)) a =
                        pendingDegree L a + pendingDegree L b := by
                    induction L with
                    | nil => simp [pendingDegree]
                    | cons f L ihL => simp [pendingDegree, hsingleA, ihL]; omega
                  have hsingleOther (v : Nat) (hva : v ≠ a) (hvb : v ≠ b) (f : Edge) :
                      incidence (contractEdge a b f) v = incidence f v := by
                    rcases f with ⟨x, y⟩
                    by_cases hxb : x = b <;> by_cases hyb : y = b <;>
                      simp [incidence, contractEdge, contractVertex, hxb, hyb, hva, hvb,
                        Ne.symm hva, Ne.symm hvb]
                  have hincOther (v : Nat) (hva : v ≠ a) (hvb : v ≠ b) (L : List Edge) :
                      pendingDegree (L.map (contractEdge a b)) v = pendingDegree L v := by
                    induction L with
                    | nil => simp
                    | cons f L ihL => simp [pendingDegree, hsingleOther v hva hvb, ihL]
                  have hdegA :
                      degree (E.map (contractEdge a b)) (contractLoops ell a b) a =
                        degree E ell a + degree E ell b + 2 := by
                    simp only [degree]
                    rw [hincA]
                    simp [contractLoops, hab]
                    omega
                  have hdegOther (v : Nat) (hva : v ≠ a) (hvb : v ≠ b) :
                      degree (E.map (contractEdge a b)) (contractLoops ell a b) v =
                        degree E ell v := by
                    simp only [degree]
                    rw [hincOther v hva hvb]
                    simp [contractLoops, hva, hvb]
                  have hc := ih (E.map (contractEdge a b)).length
                    (by simpa using hlt) (V.erase b) (E.map (contractEdge a b))
                    (contractLoops ell a b) rfl hcontract
                  have hd := ih E.length hlt V E ell rfl htail
                  rw [loopyAux]
                  simp only [if_neg hab, map_add, map_mul]
                  rw [hc, hd]
                  have hcoefficient :
                      degreeSpecialization (MvPolynomial.C Polynomial.X) = Polynomial.X := by
                    simp [degreeSpecialization]
                  rw [hcoefficient]
                  have habV : b ∈ V.erase a := by simp [hbV, Ne.symm hab]
                  have haErase : a ∈ V.erase b := by simp [haV, hab]
                  let R : Polynomial Int :=
                    ∏ v ∈ (V.erase b).erase a, geometricSum (degree E ell v + 1)
                  have hcontractProd :
                      (∏ v ∈ V.erase b,
                        geometricSum
                          (degree (E.map (contractEdge a b)) (contractLoops ell a b) v + 1)) =
                        geometricSum (degree E ell a + degree E ell b + 3) * R := by
                    rw [← Finset.mul_prod_erase (V.erase b)
                      (fun v => geometricSum
                        (degree (E.map (contractEdge a b)) (contractLoops ell a b) v + 1))
                      haErase]
                    rw [hdegA]
                    congr 1
                    apply Finset.prod_congr rfl
                    intro v hv
                    have hva : v ≠ a := (Finset.mem_erase.mp hv).1
                    have hvb : v ≠ b :=
                      (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
                    rw [hdegOther v hva hvb]
                  have hdeleteProd :
                      (∏ v ∈ V, geometricSum (degree E ell v + 1)) =
                        geometricSum (degree E ell a + 1) *
                          geometricSum (degree E ell b + 1) * R := by
                    rw [← Finset.mul_prod_erase V
                      (fun v => geometricSum (degree E ell v + 1)) haV]
                    rw [← Finset.mul_prod_erase (V.erase a)
                      (fun v => geometricSum (degree E ell v + 1)) habV]
                    simp only [R]
                    rw [Finset.erase_right_comm]
                    ring
                  have horiginalProd :
                      (∏ v ∈ V, geometricSum (degree ((a, b) :: E) ell v + 1)) =
                        geometricSum (degree E ell a + 2) *
                          geometricSum (degree E ell b + 2) * R := by
                    rw [← Finset.mul_prod_erase V
                      (fun v => geometricSum (degree ((a, b) :: E) ell v + 1)) haV]
                    rw [← Finset.mul_prod_erase (V.erase a)
                      (fun v => geometricSum (degree ((a, b) :: E) ell v + 1)) habV]
                    have hdegreeA : degree ((a, b) :: E) ell a + 1 = degree E ell a + 2 := by
                      simp [degree, pendingDegree, incidence, hab, Ne.symm hab]
                      omega
                    have hdegreeB : degree ((a, b) :: E) ell b + 1 = degree E ell b + 2 := by
                      simp [degree, pendingDegree, incidence, hab, Ne.symm hab]
                      omega
                    have hrest :
                        (∏ v ∈ (V.erase a).erase b,
                          geometricSum (degree ((a, b) :: E) ell v + 1)) = R := by
                      simp only [R]
                      rw [Finset.erase_right_comm]
                      apply Finset.prod_congr rfl
                      intro v hv
                      have hva : v ≠ a := (Finset.mem_erase.mp hv).1
                      have hvb : v ≠ b :=
                        (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
                      simp [degree, pendingDegree, incidence, hva, hvb, Ne.symm hva,
                        Ne.symm hvb]
                    rw [hrest]
                    rw [hdegreeA, hdegreeB]
                    ring
                  rw [hcontractProd, hdeleteProd, horiginalProd]
                  have hgeom :
                      geometricSum (degree E ell a + 2) *
                          geometricSum (degree E ell b + 2) =
                        Polynomial.X * geometricSum (degree E ell a + 1) *
                            geometricSum (degree E ell b + 1) +
                          geometricSum (degree E ell a + degree E ell b + 3) := by
                    have hp : (degree E ell a + 1) + 1 = degree E ell a + 2 := by omega
                    have hq : (degree E ell b + 1) + 1 = degree E ell b + 2 := by omega
                    have hpq :
                        (degree E ell a + 1) + (degree E ell b + 1) + 1 =
                          degree E ell a + degree E ell b + 3 := by omega
                    rw [← hp, ← hq, ← hpq]
                    exact geometric_identity (degree E ell a + 1) (degree E ell b + 1)
                  rw [hgeom]
                  ring
      rw [loopy]
      exact core E.length V E ell rfl hvalid
    · intro V E ell hendpoints
      classical
      have orderCore : ∀ n : Nat, ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat),
          E.length = n → (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) →
          Polynomial.IsMonicOfDegree (orderSpecialization (loopyAux V E ell)) V.card := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            intro V E ell hlen hendpoints
            cases E with
            | nil =>
                simpa [loopyAux, orderSpecialization] using
                  (Polynomial.isMonicOfDegree_X_pow (R := Int) V.card)
            | cons e E =>
                rcases e with ⟨a, b⟩
                have hhead := hendpoints (a, b) (by simp)
                have haV : a ∈ V := hhead.1
                have hbV : b ∈ V := hhead.2
                have htail : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V := by
                  intro e he
                  exact hendpoints e (by simp [he])
                have hlt : E.length < n := by
                  have hsucc : E.length + 1 = n := by simpa using hlen
                  omega
                by_cases hab : a = b
                · subst b
                  simpa only [loopyAux, ↓reduceIte] using
                    ih E.length hlt V E (addLoop ell a) rfl htail
                · have hcontractEndpoints :
                      ∀ e ∈ E.map (contractEdge a b), e.1 ∈ V.erase b ∧ e.2 ∈ V.erase b := by
                    intro e he
                    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
                    have hfV := htail f hf
                    have map_mem (x : Nat) (hx : x ∈ V) :
                        contractVertex a b x ∈ V.erase b := by
                      by_cases hxb : x = b
                      · subst x
                        simp [contractVertex, haV, hab]
                      · simp [contractVertex, hxb, hx]
                    exact And.intro (map_mem f.1 hfV.1) (map_mem f.2 hfV.2)
                  have hc := ih (E.map (contractEdge a b)).length (by simpa using hlt)
                    (V.erase b) (E.map (contractEdge a b)) (contractLoops ell a b) rfl
                    hcontractEndpoints
                  have hd := ih E.length hlt V E ell rfl htail
                  have hcard := Finset.card_erase_add_one hbV
                  have hdegree :
                      (orderSpecialization
                        (loopyAux (V.erase b) (E.map (contractEdge a b))
                          (contractLoops ell a b))).natDegree < V.card := by
                    rw [hc.natDegree_eq]
                    omega
                  simpa [loopyAux, hab, orderSpecialization] using
                    (Polynomial.IsMonicOfDegree.add_left hdegree hd)
      exact orderCore E.length V E ell rfl hendpoints
    
  rcases localFacts with ⟨hproduct, horder⟩
  have hPV := hproduct V E ell hG
  have hPW := hproduct W F eta hH
  have hOV := horder V E ell hG.1
  have hOW := horder W F eta hH.1
  have hcard : V.card = W.card := by
    have hU : orderSpecialization (loopy V E ell) =
        orderSpecialization (loopy W F eta) := by
      exact congrArg orderSpecialization hL
    have hOVd := hOV.natDegree_eq
    have hOWd := hOW.natDegree_eq
    rw [hU] at hOVd
    omega
  have hP :
      degreeSpecialization (loopy V E ell) =
        degreeSpecialization (loopy W F eta) := by
    exact congrArg degreeSpecialization hL
  have hQfactor :
      ∀ (A : Finset Nat) (L : List Edge) (l : Nat → Nat),
        degreeSpecialization (loopy A L l) =
          ∏ v ∈ A, geometricSum (degree L l v + 1) →
        (1 - (Polynomial.X : Polynomial Int)) ^ A.card *
            degreeSpecialization (loopy A L l) =
          ((degreeMultiset A L l).map
            (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod := by
    intro A L l hprod
    have hgeom (r : Nat) :
        (1 - (Polynomial.X : Polynomial Int)) * geometricSum (r + 1) =
          1 - Polynomial.X ^ (r + 1) := by
      rw [mul_comm]
      exact geom_sum_mul_neg Polynomial.X (r + 1)
    rw [hprod]
    calc
      (1 - (Polynomial.X : Polynomial Int)) ^ A.card *
            ∏ v ∈ A, geometricSum (degree L l v + 1) =
          (∏ v ∈ A, (1 - (Polynomial.X : Polynomial Int))) *
            ∏ v ∈ A, geometricSum (degree L l v + 1) := by
        rw [Finset.prod_const]
      _ = ∏ v ∈ A,
            ((1 - (Polynomial.X : Polynomial Int)) *
              geometricSum (degree L l v + 1)) := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ v ∈ A,
            (1 - (Polynomial.X : Polynomial Int) ^ (degree L l v + 1)) := by
        apply Finset.prod_congr rfl
        intro v hv
        exact hgeom (degree L l v)
      _ = ((degreeMultiset A L l).map
            (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod := by
        change (A.1.map
          (fun v => 1 - (Polynomial.X : Polynomial Int) ^ (degree L l v + 1))).prod = _
        simp [degreeMultiset, Multiset.map_map]
  have hqV := hQfactor V E ell hPV
  have hqW := hQfactor W F eta hPW
  let q : Polynomial Int :=
    (1 - (Polynomial.X : Polynomial Int)) ^ V.card *
      degreeSpecialization (loopy V E ell)
  have hqW' : q =
      ((degreeMultiset W F eta).map
        (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod := by
    dsimp [q]
    calc
      (1 - (Polynomial.X : Polynomial Int)) ^ V.card *
          degreeSpecialization (loopy V E ell) =
        (1 - (Polynomial.X : Polynomial Int)) ^ W.card *
          degreeSpecialization (loopy W F eta) := by
            rw [hcard, hP]
      _ = ((degreeMultiset W F eta).map
          (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod :=
        hqW
  have hqV' : q =
      ((degreeMultiset V E ell).map
        (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod :=
    hqV
  have heuler (m a : Nat) (hm : m ≠ 0) :
      D5.S1.Recurrence.Witt.PrimitiveEulerLedger.eulerFactor m (-Int.ofNat a) =
        (1 - (PowerSeries.X : Int⟦X⟧) ^ m) ^ a := by
    calc
      D5.S1.Recurrence.Witt.PrimitiveEulerLedger.eulerFactor m (-Int.ofNat a) =
          PowerSeries.expand m hm
            (PowerSeries.rescale (-1)
              (PowerSeries.binomialSeries Int (a : Int))) := by
        ext k
        rw [D5.S1.Recurrence.Witt.PrimitiveEulerLedger.coeff_eulerFactor,
          PowerSeries.coeff_expand]
        · by_cases hmk : m ∣ k
          · rw [if_pos hmk]
            obtain ⟨j, hj⟩ := hmk
            rw [hj, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]
            simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff]
            simp
          · simp only [if_neg hmk]
      _ = (1 - (PowerSeries.X : Int⟦X⟧) ^ m) ^ a := by
        rw [PowerSeries.binomialSeries_nat]
        rw [map_pow, map_pow, map_add, map_one,
          PowerSeries.rescale_neg_one_X]
        have hbase :
            PowerSeries.expand m hm (1 + (- (PowerSeries.X : Int⟦X⟧))) =
              1 - (PowerSeries.X : Int⟦X⟧) ^ m := by
          rw [map_add, map_one, map_neg, PowerSeries.expand_X]
          ring
        exact congrArg (fun z : Int⟦X⟧ => z ^ a) hbase
  have coeff_multiset (k : Nat) (s : Multiset Nat) (phi : Int⟦X⟧)
      (hs : ∀ d ∈ s, k < d + 1) :
      PowerSeries.coeff k
          (phi * (s.map
            (fun d => 1 - (PowerSeries.X : Int⟦X⟧) ^ (d + 1))).prod) =
        PowerSeries.coeff k phi := by
    induction s using Multiset.induction_on generalizing phi with
    | empty => simp
    | @cons d s ih =>
        have hd : k < d + 1 := hs d (by simp)
        have hs' : ∀ x ∈ s, k < x + 1 := by
          intro x hx
          exact hs x (by simp [hx])
        rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc]
        rw [ih (phi * (1 - (PowerSeries.X : Int⟦X⟧) ^ (d + 1))) hs']
        apply PowerSeries.coeff_mul_one_sub_of_lt_order
        rw [PowerSeries.order_X_pow]
        exact_mod_cast hd
  have map_coe (D : Multiset Nat) :
      (D.map (fun d => 1 - (PowerSeries.X : Int⟦X⟧) ^ (d + 1))).prod =
        (((D.map (fun d => (1 : Polynomial Int) -
            (Polynomial.X : Polynomial Int) ^ (d + 1))).prod : Polynomial Int) :
          Int⟦X⟧) := by
    induction D using Multiset.induction_on with
    | empty => simp
    | @cons d s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [ih]
        simp
  have represents_adapter (D : Multiset Nat) (p : Polynomial Int)
      (hp : p = (D.map
        (fun d => 1 - (Polynomial.X : Polynomial Int) ^ (d + 1))).prod) :
      D5.S1.Recurrence.Witt.PrimitiveEulerLedger.Represents
        (p : Int⟦X⟧) (fun r => -Int.ofNat (D.count r)) := by
    intro N k hk
    let g : Nat → Int⟦X⟧ :=
      fun d => 1 - (PowerSeries.X : Int⟦X⟧) ^ (d + 1)
    let S := D.filter (fun d => d < N)
    let T := D.filter (fun d => ¬ d < N)
    have hprefix :
        D5.S1.Recurrence.Witt.PrimitiveEulerLedger.ledgerProduct
            (fun r => -Int.ofNat (D.count r)) N = (S.map g).prod := by
      calc
        D5.S1.Recurrence.Witt.PrimitiveEulerLedger.ledgerProduct
              (fun r => -Int.ofNat (D.count r)) N =
            ∏ n ∈ Finset.range N, g n ^ D.count n := by
          apply Finset.prod_congr rfl
          intro n hn
          exact heuler (n + 1) (D.count n) (by omega)
        _ = ∏ d ∈ Finset.range N, g d ^ D.count d := rfl
        _ = ∏ d ∈ S.toFinset, g d ^ D.count d := by
          symm
          apply Finset.prod_subset
            (fun d hd => Finset.mem_range.mpr (Multiset.mem_filter.mp
              (Multiset.mem_toFinset.mp hd)).2)
          intro d hd hnot
          have hdm : d ∉ S := by
            intro hds
            exact hnot (Multiset.mem_toFinset.mpr hds)
          simp [Multiset.count_eq_zero_of_notMem (fun hmem =>
            hdm (Multiset.mem_filter.mpr ⟨hmem, Finset.mem_range.mp hd⟩))]
        _ = ∏ d ∈ S.toFinset, g d ^ S.count d := by
          apply Finset.prod_congr rfl
          intro d hd
          have hc : S.count d = D.count d := by
            dsimp [S]
            exact Multiset.count_filter_of_pos (Multiset.mem_filter.mp
              (Multiset.mem_toFinset.mp hd)).2
          rw [hc]
        _ = (S.map g).prod := (Finset.prod_multiset_map_count S g).symm
    have hst : S + T = D := by
      dsimp [S, T]
      exact Multiset.filter_add_not (fun d => d < N) D
    have hfilter : (S.map g).prod * (T.map g).prod = (D.map g).prod := by
      calc
        (S.map g).prod * (T.map g).prod =
            (S.map g + T.map g).prod := (Multiset.prod_add _ _).symm
        _ = ((S + T).map g).prod := by rw [Multiset.map_add]
        _ = (D.map g).prod := by rw [hst]
    have htail : ∀ d ∈ T, k < d + 1 := by
      intro d hd
      have hdN := (Multiset.mem_filter.mp hd).2
      omega
    have hcoef :
        PowerSeries.coeff k ((S.map g).prod * (T.map g).prod) =
          PowerSeries.coeff k (S.map g).prod := by
      exact coeff_multiset k T ((S.map g).prod) htail
    calc
      PowerSeries.coeff k
          (D5.S1.Recurrence.Witt.PrimitiveEulerLedger.ledgerProduct
            (fun r => -Int.ofNat (D.count r)) N) =
          PowerSeries.coeff k ((S.map g).prod) := by rw [hprefix]
      _ = PowerSeries.coeff k ((D.map g).prod) := by rw [← hfilter, hcoef]
      _ = PowerSeries.coeff k (p : Int⟦X⟧) := by
        rw [hp]
        have hmap : (D.map g).prod =
            (((D.map (fun d => (1 : Polynomial Int) -
                (Polynomial.X : Polynomial Int) ^ (d + 1))).prod : Polynomial Int) :
              Int⟦X⟧) :=
          by simpa [g] using map_coe D
        rw [hmap]
  let DV := degreeMultiset V E ell
  let DW := degreeMultiset W F eta
  let cV : Nat → Int := fun r => -Int.ofNat (DV.count r)
  let cW : Nat → Int := fun r => -Int.ofNat (DW.count r)
  have hconstPS : ∀ s : Multiset Nat,
      PowerSeries.constantCoeff
          ((s.map (fun d => 1 - (PowerSeries.X : Int⟦X⟧) ^ (d + 1))).prod) = 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons d s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
        rw [ih]
        simp
  have hqconst : PowerSeries.constantCoeff (q : Int⟦X⟧) = 1 := by
    rw [hqV', ← map_coe]
    exact hconstPS _
  have hrepV :
      D5.S1.Recurrence.Witt.PrimitiveEulerLedger.Represents
        (q : Int⟦X⟧) cV := by
    exact represents_adapter DV q (by simpa [DV] using hqV')
  have hrepW :
      D5.S1.Recurrence.Witt.PrimitiveEulerLedger.Represents
        (q : Int⟦X⟧) cW := by
    exact represents_adapter DW q (by simpa [DW] using hqW')
  have hcEq : cV = cW := by
    exact
      (D5.S1.Recurrence.Witt.PrimitiveEulerLedger.unique_primitive_euler_ledger
        (q : Int⟦X⟧) hqconst).unique hrepV hrepW
  apply Multiset.ext'
  intro r
  have hr := congrFun hcEq r
  dsimp [cV, cW, DV, DW] at hr
  exact Int.ofNat_inj.mp (neg_inj.mp hr)

end
end D5.S3.Factorization.Combinatorics.LoopyDegreeSequence
