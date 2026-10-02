/- GID: D5/S3/Quantum/Recovery/FiniteLocalFrontierMoment
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalFrontierMoment
   mirror-E: none(waiver:finite-frontier-moments)
   anchors: []
   utility: none
   digest: One finite labelled tree carries the source defect budget and stopped second moments. -/
import D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open FiniteLocalLatitudeGeometry
set_option autoImplicit false
set_option maxRecDepth 4000
def Z (r : ℝ) := 1-4*h r
def H (r : ℝ) := Z r*(1-kappa r)/(2*kappa r)
def tau (r : ℝ) := H r/4
def epsilon (r : ℝ) := H r^2/8192
def U (r : ℝ) := 1/(3*kappa r)
abbrev origin : State := (⟨0,by simp⟩,⟨0,by simp⟩)
def polarMoment (z : State) := ((z.1 : Bloch) 2 ^ 2 + (z.2 : Bloch) 2 ^ 2)/2
def Tree.Cut.include {z : State} {T : Tree z} (cut : T.Cut) :
    ∀ v : cut.Nodes, (cut.branch v).2.Leaves → T.Leaves :=
  match cut with
  | .here _ => fun _ l => l
  | .descend _ _ _ _ _ cuts => fun v l => ⟨v.1,(cuts v.1).include v.2 l⟩
def successMass {z : State} (T : Tree z) (mark : T.Leaves → Bool) :=
  T.expect (fun l => if mark l then 1 else 0)
def failureDefect {z : State} (T : Tree z) (mark : T.Leaves → Bool) :=
  T.expect (fun l => if mark l then 0 else d (T.endpoint l))
def frontierMass {z : State} {T : Tree z} (cut : T.Cut) (r epsilon tau : ℝ) : ℝ :=
  ∑ v, if d (cut.branch v).1 = epsilon ∧ Z r+tau ≤ polarMoment (cut.branch v).1
    then cut.mass v else 0

set_option maxHeartbeats 6000000 in
/-- Conservation, the source second-moment excess, and stopped conditional
variance all concern this one complete labelled tree and this one success set. -/
theorem same_tree_stopped_moment_certificate (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) (z : State) (T : Tree z)
    (mark : T.Leaves → Bool)
    (accepted : ∀ l, mark l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r) :
    (0 ≤ failureDefect T mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark)) ∧
    4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
    U r-H r^3/(49152*kappa r) < U r ∧
    H r^3/(196608*kappa r) ≤ psi r origin := by
  classical
  have certificateAll : ∀ (z : State) (T : Tree z) (mark : T.Leaves → Bool)
      (accepted : ∀ l, mark l = true →
        (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r),
    0 ≤ failureDefect T mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark) := by
    intro z T mark accepted
    classical
    have bn (a : Ball) : ‖(a : Bloch)‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using a.property
    have dn (z : State) : 0 ≤ d z := by
      have hi := real_inner_le_norm (z.1 : Bloch) (z.2 : Bloch)
      have hh : ‖(z.1 : Bloch)‖*‖(z.2 : Bloch)‖ ≤ 1 := by nlinarith [bn z.1,bn z.2,norm_nonneg (z.1 : Bloch),norm_nonneg (z.2 : Bloch)]
      dsimp [d,defect]; linarith
    have constant : ∀ {z : State} (T : Tree z) (c : ℝ), T.expect (fun _ => c) = c := by
      intro z T
      induction T with
      | stop => intro c; rfl
      | node actor z m s next ih =>
        intro c; simp only [Tree.expect,ih,← Finset.sum_mul,s.total,one_mul]
    have linear : ∀ {z : State} (T : Tree z) (F G : T.Leaves → ℝ) (a b : ℝ),
        T.expect (fun l => a*F l+b*G l) = a*T.expect F+b*T.expect G := by
      intro z T
      induction T with
      | stop => intros; rfl
      | node actor z m s next ih =>
        intro F G a b; simp only [Tree.expect,ih,mul_add,Finset.sum_add_distrib]
        simp_rw [← mul_assoc,mul_comm (s.w _ ) a,mul_comm (s.w _) b,mul_assoc]
        rw [← Finset.mul_sum,← Finset.mul_sum]
    have mono : ∀ {z : State} (T : Tree z) (F G : T.Leaves → ℝ),
        (∀ l, F l ≤ G l) → T.expect F ≤ T.expect G := by
      intro z T
      induction T with
      | stop => intro F G hh; exact hh ()
      | node actor z m s next ih =>
        intro F G hh; exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (ih i _ _ (fun l => hh ⟨i,l⟩)) (s.nonneg i)
    have nonneg : ∀ {z : State} (T : Tree z) (F : T.Leaves → ℝ),
        (∀ l, 0 ≤ F l) → 0 ≤ T.expect F := by
      intro z T F hh
      simpa only [constant] using mono T (fun _ => 0) F hh
    have splitMean (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z))
        (j : Fin 3) : (∑ i, s.w i * (s.x i : Bloch) j) = (active actor z : Bloch) j := by
      have hh := congrArg (fun x : Bloch => x j) s.mean
      simpa using hh
    have affine : ∀ (L : State → ℝ),
        (∀ actor z m (s : Split m (active actor z)),
          (∑ i, s.w i * L (place actor (s.x i) (passive actor z))) = L z) →
        ∀ {z : State} (T : Tree z), T.expect (fun l => L (T.endpoint l)) = L z := by
      intro L hh z T
      induction T with
      | stop => rfl
      | node actor z m s next ih =>
        simp only [Tree.expect,Tree.endpoint,ih]; exact hh actor z m s
    have daffine (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z)) :
        (∑ i, s.w i * d (place actor (s.x i) (passive actor z))) = d z := by
      have hi : (∑ i, s.w i * inner ℝ (s.x i : Bloch) (passive actor z : Bloch)) =
          inner ℝ (active actor z : Bloch) (passive actor z : Bloch) := by
        rw [← s.mean,sum_inner]; simp_rw [real_inner_smul_left]
      cases actor
      · change Split m z.1 at s
        simp only [place,active,passive,Bool.false_eq_true,↓reduceIte] at hi ⊢; simp only [d,defect,mul_div,mul_sub,mul_one,← Finset.sum_div,Finset.sum_sub_distrib]
        rw [s.total,hi]
      · change Split m z.2 at s; simp only [place,active,passive,↓reduceIte] at hi ⊢
        have hj : (∑ i, s.w i * inner ℝ (z.1 : Bloch) (s.x i : Bloch)) =
            inner ℝ (z.1 : Bloch) (z.2 : Bloch) := by
          rw [← s.mean,inner_sum]; simp_rw [real_inner_smul_right]
        simp only [d,defect,mul_div,mul_sub,mul_one,
          ← Finset.sum_div,Finset.sum_sub_distrib]
        rw [s.total,hj]
    have pzaffine (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z)) :
        (∑ i, s.w i * (((place actor (s.x i) (passive actor z)).1 : Bloch) 2 *
          ((place actor (s.x i) (passive actor z)).2 : Bloch) 2)) =
          (z.1 : Bloch) 2 * (z.2 : Bloch) 2 := by
      have hi := splitMean actor z m s 2
      cases actor
      · change Split m z.1 at s; simp only [place,active,passive,Bool.false_eq_true,↓reduceIte] at hi ⊢
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul,hi]
      · change Split m z.2 at s; simp only [place,active,passive,↓reduceIte] at hi ⊢
        have hfun (i : Fin m) : s.w i*((z.1 : Bloch) 2*(s.x i : Bloch) 2) =
            (z.1 : Bloch) 2*(s.w i*(s.x i : Bloch) 2) := by ring
        simp_rw [hfun]
        rw [← Finset.mul_sum,hi]
    have dconserve := affine d daffine T
    have pzconserve := affine (fun q => (q.1 : Bloch) 2*(q.2 : Bloch) 2) pzaffine T
    have splitSquare (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z))
        (j : Fin 3) : (active actor z : Bloch) j ^ 2 ≤
        ∑ i, s.w i * (s.x i : Bloch) j ^ 2 := by
      have hh := (Even.convexOn_pow (by decide : Even 2)).map_sum_le
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => s.nonneg i)
        s.total (fun _ _ => Set.mem_univ _) (p := fun i => (s.x i : Bloch) j)
      simpa only [smul_eq_mul,splitMean actor z m s j] using hh
    let roof := fun q : State => 1-((q.1 : Bloch) 0^2+(q.1 : Bloch) 1^2+
      (q.2 : Bloch) 0^2+(q.2 : Bloch) 1^2)/2
    have roofConcave : SeparatelyConcave roof := by
      intro actor z m s
      have h0 := splitSquare actor z m s 0
      have h1 := splitSquare actor z m s 1
      cases actor <;>
        simp only [roof,place,active,passive,Bool.false_eq_true,↓reduceIte,mul_sub,
          mul_div,mul_add,mul_one,Finset.sum_sub_distrib,Finset.sum_add_distrib,
          ← Finset.sum_div,← Finset.sum_mul,s.total,one_mul] at * <;> linarith
    have roofBound : ∀ {z : State} (T : Tree z),
        T.expect (fun l => roof (T.endpoint l)) ≤ roof z := by
      intro z T
      induction T with
      | stop => exact le_rfl
      | node actor z m s next ih =>
        exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih i) (s.nonneg i)).trans
          (roofConcave actor z m s)
    have normeq (a : Ball) : ‖(a : Bloch)‖^2 = (a : Bloch) 0^2+(a : Bloch) 1^2+(a : Bloch) 2^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_three]
    have roofeq (z : State) : roof z = polarMoment z +
        (2-‖(z.1 : Bloch)‖^2-‖(z.2 : Bloch)‖^2)/2 := by
      rw [normeq,normeq]; dsimp [roof,polarMoment]; ring
    have variance : ∀ {z : State} (T : Tree z),
        T.expect (fun l => polarMoment (T.endpoint l)) ≤ roof z := by
      intro z T
      apply (mono T _ _ (fun l => ?_)).trans (roofBound T)
      rw [roofeq]
      have ha := bn (T.endpoint l).1
      have hb := bn (T.endpoint l).2
      have hna := norm_nonneg ((T.endpoint l).1 : Bloch)
      have hnb := norm_nonneg ((T.endpoint l).2 : Bloch)
      nlinarith
    have cutlaw : ∀ {z : State} {T : Tree z} (cut : T.Cut) (F : T.Leaves → ℝ),
        T.expect F = ∑ v, cut.mass v *
          (cut.branch v).2.expect (fun l => F (cut.include v l)) := by
      intro z T cut
      induction cut with
      | here T =>
        intro F
        change T.expect F = ∑ _ : Unit, 1*T.expect F
        simp
      | descend actor z m s next cuts ih =>
        intro F; simp only [Tree.expect]
        simp_rw [ih,Finset.mul_sum]
        change (∑ i, ∑ v, s.w i*((cuts i).mass v *
          ((cuts i).branch v).2.expect (fun l => F ⟨i,(cuts i).include v l⟩))) =
          ∑ v : ((i : Fin m) × (cuts i).Nodes),
            (s.w v.1*(cuts v.1).mass v.2)*
              ((cuts v.1).branch v.2).2.expect (fun l => F ⟨v.1,(cuts v.1).include v.2 l⟩)
        rw [Fintype.sum_sigma]; simp only [mul_assoc]
    have cutEndpoint : ∀ {z : State} {T : Tree z} (cut : T.Cut) (v : cut.Nodes) l,
        T.endpoint (cut.include v l) = (cut.branch v).2.endpoint l := by
      intro z T cut
      induction cut with
      | here => intros; rfl
      | descend actor z m s next cuts ih => intro v l; exact ih v.1 v.2 l
    have cutNonneg : ∀ {z : State} {T : Tree z} (cut : T.Cut) (v : cut.Nodes), 0 ≤ cut.mass v := by
      intro z T cut
      induction cut with
      | here => intro v; exact zero_le_one
      | descend actor z m s next cuts ih => intro v; exact mul_nonneg (s.nonneg v.1) (ih v.1 v.2)
    have flat (l : T.Leaves) (hl : mark l = true) :=
      (all_r_flat_geometry r hr hlo hhi).2.2.2.2 _ _ (accepted l hl)
    have budgetAll (q : State) (R : Tree q) (m : R.Leaves → Bool)
        (acc : ∀ l, m l = true → (((R.endpoint l).1 : Bloch),((R.endpoint l).2 : Bloch)) ∈ K_s r) :
        g r*successMass R m+failureDefect R m = d q := by
      have dc := affine d daffine R
      rw [← dc]
      unfold successMass failureDefect
      conv_lhs => rhs; rw [← one_mul (R.expect _)]
      rw [← linear R _ _ (g r) 1]
      congr 1; funext l
      cases hh : m l
      · simp [hh]
      · have hg := (all_r_flat_geometry r hr hlo hhi).2.2.2.2 _ _ (acc l hh); simp [hh,d,hg.2.2]
    have budget := budgetAll z T mark accepted
    have rootExcess : z = (⟨0,by simp⟩,⟨0,by simp⟩) →
        H r-(2*Z r/g r)*failureDefect T mark ≤
          T.expect (fun l => polarMoment (T.endpoint l))-Z r := by
      intro hz
      have hzprod : (z.1 : Bloch) 2*(z.2 : Bloch) 2 = 0 := by rw [hz]; simp
      rw [hzprod] at pzconserve
      have hzdef : d z = 1/4 := by rw [hz]; simp [d,defect]
      rw [hzdef] at budget
      have pointwise (l : T.Leaves) :
          2*Z r*(if mark l then 1 else 0) + ((T.endpoint l).1 : Bloch) 2*((T.endpoint l).2 : Bloch) 2 ≤
            polarMoment (T.endpoint l) := by
        cases hh : mark l
        · simp only [hh,Bool.false_eq_true,↓reduceIte,mul_zero,zero_add]; dsimp [polarMoment]; nlinarith [sq_nonneg (((T.endpoint l).1 : Bloch) 2-((T.endpoint l).2 : Bloch) 2)]
        · have hf := flat l hh; simp only [hh,↓reduceIte,mul_one]; dsimp [polarMoment,Z]
          have hb : ((T.endpoint l).2 : Bloch) 2 ^ 2 = 1-4*h r := by
            rw [hf.1] at hf; nlinarith [hf.2.1]
          nlinarith [hf.1,hf.2.1,hb]
      have hm := mono T _ _ pointwise
      have reform : (fun l => 2*Z r*(if mark l then (1 : ℝ) else 0) +
        ((T.endpoint l).1 : Bloch) 2*((T.endpoint l).2 : Bloch) 2) =
        (fun l => 2*Z r*(if mark l then 1 else 0)+1*
          (((T.endpoint l).1 : Bloch) 2*((T.endpoint l).2 : Bloch) 2)) := by funext l; ring
      rw [reform] at hm; rw [linear T _ _ (2*Z r) 1] at hm; rw [pzconserve] at hm
      change 2*Z r*successMass T mark+1*0 ≤ _ at hm
      have kp : 0 < kappa r := by unfold kappa; positivity
      have gp : 0 < g r := by unfold g; positivity
      have hp : 0 < 1+kappa r := by positivity
      have hid : Z r*(1-2*g r)/(2*g r) = H r := by unfold H g; field_simp [ne_of_gt kp,ne_of_gt hp]; ring
      have hS : successMass T mark = (1/4-failureDefect T mark)/g r := by apply (eq_div_iff (ne_of_gt gp)).mpr; linarith [budget]
      rw [hS] at hm
      have hex : 2*Z r*((1/4-failureDefect T mark)/g r)-Z r =
          H r-(2*Z r/g r)*failureDefect T mark := by
        rw [← hid]; field_simp [ne_of_gt gp]; ring
      linarith
    have frontierBound : ∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
        (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
          (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
        z = (⟨0,by simp⟩,⟨0,by simp⟩) →
        H r-(2*Z r/g r)*failureDefect T mark ≤
          tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon := by
      intro epsilon tau he ht cut hcut hz
      have kp : 0 < kappa r := by unfold kappa; positivity
      have kmin : 2/3 ≤ kappa r := by
        have hin : 0 ≤ 4+2*(r^2+(r^2)⁻¹) := by positivity
        have hs := Real.sq_sqrt hin
        have hn := Real.sqrt_nonneg (4+2*(r^2+(r^2)⁻¹))
        have hi : 0 ≤ (r^2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
        unfold kappa; nlinarith [sq_nonneg r]
      have hp : 0 ≤ h r := by unfold h; positivity
      have hple : h r ≤ 1/4 := by
        unfold h
        apply (div_le_iff₀ (by positivity : 0 < 3*(1+kappa r))).mpr
        linarith
      have zn : 0 ≤ Z r := by dsimp [Z]; linarith
      have cb (q : State) : polarMoment q ≤ 1 := by
        have ha := normeq q.1
        have hb := normeq q.2
        have hna := bn q.1
        have hnb := bn q.2
        have nna := norm_nonneg (q.1 : Bloch)
        have nnb := norm_nonneg (q.2 : Bloch)
        dsimp [polarMoment]; nlinarith [sq_nonneg ((q.1 : Bloch) 0),sq_nonneg ((q.1 : Bloch) 1),
          sq_nonneg ((q.2 : Bloch) 0),sq_nonneg ((q.2 : Bloch) 1)]
      have threshold (q : State) (hd : d q = epsilon) : roof q ≤ polarMoment q+8*epsilon := by
        have dot : inner ℝ (q.1 : Bloch) (q.2 : Bloch) = 1-4*epsilon := by dsimp [d,defect] at hd; linarith
        have hi := real_inner_le_norm (q.1 : Bloch) (q.2 : Bloch)
        have hm1 : ‖(q.1 : Bloch)‖*‖(q.2 : Bloch)‖ ≤ ‖(q.1 : Bloch)‖ :=
          mul_le_of_le_one_right (norm_nonneg _) (bn q.2)
        have hm2 : ‖(q.1 : Bloch)‖*‖(q.2 : Bloch)‖ ≤ ‖(q.2 : Bloch)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (bn q.1)
        rw [roofeq]; nlinarith [sq_nonneg (1-‖(q.1 : Bloch)‖),sq_nonneg (1-‖(q.2 : Bloch)‖)]
      have terminalBound : ∀ {q : State} (R : Tree q) (m : R.Leaves → Bool),
          R.depth = 0 →
          (∀ l, m l = true → (((R.endpoint l).1 : Bloch),((R.endpoint l).2 : Bloch)) ∈ K_s r) →
          epsilon < d q →
          R.expect (fun l => polarMoment (R.endpoint l))-Z r ≤ failureDefect R m/epsilon := by
        intro q R
        cases R with
        | stop q =>
          intro m hd acc hq
          cases hh : m ()
          · have hdiv : 1 ≤ d q/epsilon := (le_div_iff₀ he).mpr (by simpa only [one_mul] using hq.le)
            simp only [failureDefect,Tree.expect,Tree.endpoint,hh,Bool.false_eq_true,↓reduceIte]; linarith [cb q]
          · have hk := acc () hh
            change ((q.1 : Bloch),(q.2 : Bloch)) ∈ K_s r at hk
            have hg := (all_r_flat_geometry r hr hlo hhi).2.2.2.2 (q.1 : Bloch) (q.2 : Bloch) hk
            have hc : polarMoment q = Z r := by
              dsimp [polarMoment,Z]
              have hbb : (q.2 : Bloch) 2 ^ 2 = 1-4*h r := by rw [hg.1] at hg; nlinarith [hg.2.1]
              nlinarith [hg.2.1,hbb]
            simp only [failureDefect,Tree.expect,Tree.endpoint,hh,↓reduceIte,hc,sub_self,zero_div,le_refl]
        | node actor q m s next => intro _ hd; change 1+_ = 0 at hd; omega
      have massTotal : (∑ v, cut.mass v) = 1 := by
        have hh := cutlaw cut (fun _ => 1)
        simp_rw [constant,mul_one] at hh
        exact hh.symm
      have deltaCut : failureDefect T mark = ∑ v, cut.mass v *
          failureDefect (cut.branch v).2 (fun l => mark (cut.include v l)) := by
        unfold failureDefect; rw [cutlaw cut]
        congr 1; funext v; simp_rw [cutEndpoint]
      let indicator := fun v : cut.Nodes =>
        if d (cut.branch v).1 = epsilon ∧ Z r+tau ≤ polarMoment (cut.branch v).1 then (1 : ℝ) else 0
      have localBound (v : cut.Nodes) :
          cut.mass v*((cut.branch v).2.expect (fun l => polarMoment ((cut.branch v).2.endpoint l))-Z r) ≤
          cut.mass v*(tau+indicator v+8*epsilon+
            failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))/epsilon) := by
        by_cases hv : cut.mass v = 0
        · simp [hv]
        have hvp : 0 < cut.mass v := lt_of_le_of_ne (cutNonneg cut v) (Ne.symm hv)
        have fn : 0 ≤ failureDefect (cut.branch v).2 (fun l => mark (cut.include v l)) :=
          nonneg _ _ (fun l => by split_ifs; exact le_rfl; exact dn _)
        have fdn : 0 ≤ failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))/epsilon := div_nonneg fn he.le
        have inn : 0 ≤ indicator v := by dsimp [indicator]; split_ifs <;> norm_num
        apply mul_le_mul_of_nonneg_left _ (cutNonneg cut v)
        rcases hcut v hvp with hd | ⟨habove,hdepth⟩
        · have hvb := (variance (cut.branch v).2).trans (threshold (cut.branch v).1 hd)
          by_cases hc : Z r+tau ≤ polarMoment (cut.branch v).1
          · have hii : indicator v = 1 := if_pos ⟨hd,hc⟩; rw [hii]; linarith [cb (cut.branch v).1]
          · have hii : indicator v = 0 := if_neg (fun h => hc h.2); rw [hii]; linarith [lt_of_not_ge hc]
        · have hb := terminalBound (cut.branch v).2 (fun l => mark (cut.include v l)) hdepth
            (fun l hh => by simpa only [cutEndpoint] using accepted (cut.include v l) hh) habove
          linarith
      have sumBound := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => localBound v)
      have left : (∑ v, cut.mass v*((cut.branch v).2.expect
          (fun l => polarMoment ((cut.branch v).2.endpoint l))-Z r)) =
          T.expect (fun l => polarMoment (T.endpoint l))-Z r := by
        simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,massTotal,one_mul]; rw [cutlaw cut]
        simp_rw [cutEndpoint]
      have right : (∑ v, cut.mass v*(tau+indicator v+8*epsilon+
          failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))/epsilon)) =
          tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon := by
        simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,massTotal,one_mul,mul_div,
          ← Finset.sum_div,← deltaCut]
        congr 2
        simp [frontierMass,indicator,mul_ite]
      rw [left,right] at sumBound; exact (rootExcess hz).trans sumBound
    refine ⟨nonneg T _ (fun l => by split_ifs; exact le_rfl; exact dn _),budget,rootExcess,?_,?_,frontierBound,?_⟩
    · intro cut
      unfold failureDefect; rw [cutlaw cut]
      congr 1
      funext v
      simp_rw [cutEndpoint]
    · intro cut; rw [cutlaw cut]
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (cutNonneg cut v)
      simp_rw [cutEndpoint]
      rw [← roofeq]; exact variance (cut.branch v).2
    · intro cut hcut hz
      have kp : 0 < kappa r := by unfold kappa; positivity
      have kmin : 2/3 ≤ kappa r := by
        have hin : 0 ≤ 4+2*(r^2+(r^2)⁻¹) := by positivity
        have hs := Real.sq_sqrt hin
        have hn := Real.sqrt_nonneg (4+2*(r^2+(r^2)⁻¹))
        have hi : 0 ≤ (r^2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
        unfold kappa; nlinarith [sq_nonneg r]
      have kmax : kappa r < 1 := by
        have tp : 0 < r^2 := lt_trans (by norm_num) hlo
        have hprod := mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hhi)
        have hinv : r^2*(r^2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt tp)
        have hmult : r^2*(r^2+(r^2)⁻¹) < r^2*(5/2) := by nlinarith
        have hsum := (mul_lt_mul_iff_of_pos_left tp).mp hmult
        have hs := Real.sq_sqrt (show 0 ≤ 4+2*(r^2+(r^2)⁻¹) by positivity)
        have hn := Real.sqrt_nonneg (4+2*(r^2+(r^2)⁻¹))
        unfold kappa; nlinarith
      have hp : 0 < h r := by unfold h; positivity
      have hsmall : h r < 1/4 := by
        unfold h
        apply (div_lt_iff₀ (by positivity : 0 < 3*(1+kappa r))).mpr
        linarith
      have zn : 0 < Z r := by dsimp [Z]; linarith
      have zmax : Z r ≤ 1 := by dsimp [Z]; linarith
      have hn : 0 < H r := by unfold H; positivity
      have hm : H r ≤ 1 := by
        have hg : 0 ≤ 1-kappa r := sub_nonneg.mpr kmax.le
        have hprod : Z r*(1-kappa r) ≤ 1 := by nlinarith
        unfold H
        apply (div_le_iff₀ (by positivity : 0 < 2*kappa r)).mpr
        nlinarith
      have ep : 0 < epsilon r := by unfold epsilon; positivity
      have tn : 0 ≤ tau r := by unfold tau; positivity
      have esm : 8*epsilon r ≤ H r/4 := by unfold epsilon; nlinarith
      have hb := frontierBound (epsilon r) (tau r) ep tn cut hcut hz
      change H r-(2*Z r/g r)*failureDefect T mark ≤
        tau r+frontierMass cut r (epsilon r) (tau r)+8*epsilon r+failureDefect T mark/epsilon r at hb
      unfold tau at hb
      have heq : failureDefect T mark/epsilon r = (1/epsilon r)*failureDefect T mark := by ring
      rw [heq] at hb
      have wl : H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
          frontierMass cut r (epsilon r) (tau r) := by
        unfold tau; nlinarith
      have gp : 0 < g r := by unfold g; positivity
      have ghalf : g r ≤ 1/2 := by
        unfold g
        apply (div_le_iff₀ (by positivity : 0 < 1+kappa r)).mpr
        linarith
      have tsq : (tau r)^2 = 512*epsilon r := by unfold tau epsilon; ring
      have tp : 0 < tau r := by unfold tau; positivity
      have emax : epsilon r ≤ 1/8192 := by unfold epsilon; nlinarith
      have coord (x : Bloch) : x 2^2 ≤ ‖x‖^2 := by
        rw [EuclideanSpace.real_norm_sq_eq]; simp only [Fin.sum_univ_three]; nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
      have failAt : ∀ (q : State) (R : Tree q) (m : R.Leaves → Bool),
        (∀ l, m l = true → (((R.endpoint l).1 : Bloch),((R.endpoint l).2 : Bloch)) ∈ K_s r) →
        d q = epsilon r → Z r+tau r ≤ polarMoment q →
        epsilon r/2 ≤ failureDefect R m := by
        intro q R m acc hd hc
        let a : Bloch := q.1
        let b : Bloch := q.2
        have an : ‖a‖ ≤ 1 := bn q.1
        have bn' : ‖b‖ ≤ 1 := bn q.2
        have ap := norm_nonneg a
        have bp := norm_nonneg b
        have dot : inner ℝ a b = 1-4*epsilon r := by dsimp [d,defect] at hd; linarith only [hd]
        have hi := real_inner_le_norm a b
        have hmab : ‖a‖*‖b‖ ≤ ‖a‖ := mul_le_of_le_one_right ap bn'
        have ahalf : 1/2 < ‖a‖ := by nlinarith only [emax,dot,hi,hmab]
        have azb : a 2^2 ≤ 1 := by nlinarith only [coord a,an,ap]
        have bzb : b 2^2 ≤ 1 := by nlinarith only [coord b,bn',bp]
        have normdiff : ‖a-b‖^2 ≤ 8*epsilon r := by rw [norm_sub_sq_real]; nlinarith only [dot,an,bn',ap,bp]
        have diffcoord : (a 2-b 2)^2 ≤ 8*epsilon r := by
          have hh := coord (a-b)
          change (a 2-b 2)^2 ≤ ‖a-b‖^2 at hh; exact hh.trans normdiff
        have sumcoord : (a 2+b 2)^2 ≤ 4 := by nlinarith only [azb,bzb,sq_nonneg (a 2-b 2)]
        have diffpol : (a 2^2-b 2^2)^2 ≤ 32*epsilon r := by
          calc
            _ = (a 2-b 2)^2*(a 2+b 2)^2 := by ring
            _ ≤ (a 2-b 2)^2*4 := mul_le_mul_of_nonneg_left sumcoord (sq_nonneg _)
            _ ≤ 32*epsilon r := by nlinarith only [diffcoord]
        have azhigh : Z r+tau r/2 ≤ a 2^2 := by
          change Z r+tau r ≤ (a 2^2+b 2^2)/2 at hc
          have hh : b 2^2-a 2^2 ≤ tau r/4 := by nlinarith only [diffpol,tsq,tp]
          linarith only [hh,hc,tp]
        let n : Bloch := ‖a‖⁻¹ • a
        have ane : ‖a‖ ≠ 0 := by linarith
        have np : 0 < ‖a‖⁻¹ := inv_pos.mpr (by linarith)
        have nn : ‖n‖ = 1 := by
          simp only [n,norm_smul,Real.norm_eq_abs,abs_of_pos np]; exact inv_mul_cancel₀ ane
        have ncoord : ‖a‖*n 2 = a 2 := by
          change ‖a‖*(‖a‖⁻¹*a 2) = a 2
          field_simp [ane]
        have nzbig : Z r+tau r/2 ≤ n 2^2 := by
          have hae : a 2^2 = ‖a‖^2*n 2^2 := by rw [← ncoord]; ring
          have hmul : ‖a‖^2*n 2^2 ≤ n 2^2 := by
            have ha : ‖a‖^2 ≤ 1 := by nlinarith only [an,ap]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (sq_nonneg (n 2))
          linarith only [hae,hmul,azhigh]
        let qn := fun x : State => (1-inner ℝ n (x.1 : Bloch))*(1-inner ℝ n (x.2 : Bloch))/4
        have factor (x : Ball) : 0 ≤ 1-inner ℝ n (x : Bloch) := by
          have hh := real_inner_le_norm n (x : Bloch)
          rw [nn,one_mul] at hh; linarith [bn x]
        have qpositive (x : State) : 0 ≤ qn x :=
          div_nonneg (mul_nonneg (factor x.1) (factor x.2)) (by norm_num)
        have qflat (x : State) (hx : ((x.1 : Bloch),(x.2 : Bloch)) ∈ K_s r) :
            (tau r)^2/64 ≤ qn x := by
          have hg := (all_r_flat_geometry r hr hlo hhi).2.2.2.2 _ _ hx
          have xnorm := hx.1
          have ynorm := hx.2.1
          have hxx : (x.1 : Bloch) 2^2 = Z r := hg.2.1
          have hyy : (x.2 : Bloch) 2 = -(x.1 : Bloch) 2 := by linarith [hg.1]
          have hdx : (n 2-(x.1 : Bloch) 2)^2 ≤ 2*(1-inner ℝ n (x.1 : Bloch)) := by
            have hh := coord (n-(x.1 : Bloch))
            change (n 2-(x.1 : Bloch) 2)^2 ≤ ‖n-(x.1 : Bloch)‖^2 at hh; rw [norm_sub_sq_real,nn,xnorm] at hh; nlinarith only [hh]
          have hdy : (n 2-(x.2 : Bloch) 2)^2 ≤ 2*(1-inner ℝ n (x.2 : Bloch)) := by
            have hh := coord (n-(x.2 : Bloch))
            change (n 2-(x.2 : Bloch) 2)^2 ≤ ‖n-(x.2 : Bloch)‖^2 at hh; rw [norm_sub_sq_real,nn,ynorm] at hh; nlinarith only [hh]
          have ident : (n 2^2-Z r)^2 = (n 2-(x.1 : Bloch) 2)^2*(n 2-(x.2 : Bloch) 2)^2 := by rw [← hxx,hyy]; ring
          have hprod := mul_le_mul hdx hdy (sq_nonneg _) (by linarith [factor x.1])
          rw [← ident] at hprod
          have hh : tau r/2 ≤ n 2^2-Z r := by linarith only [nzbig]
          have hs : (tau r/2)^2 ≤ (n 2^2-Z r)^2 :=
            (sq_le_sq₀ (by positivity) (by linarith only [hh,tp])).mpr hh
          dsimp [qn]; nlinarith only [hs,hprod]
        have qaffine (actor : Bool) (z : State) (m' : ℕ) (s : Split m' (active actor z)) :
            (∑ i, s.w i*qn (place actor (s.x i) (passive actor z))) = qn z := by
          have hmean : (∑ i, s.w i*(1-inner ℝ n (s.x i : Bloch))) =
              1-inner ℝ n (active actor z : Bloch) := by
            have hh := congrArg (fun x : Bloch => inner ℝ n x) s.mean
            simp only [inner_sum,real_inner_smul_right] at hh; simp only [mul_sub,mul_one,Finset.sum_sub_distrib,s.total,hh]
          cases actor
          · change Split m' z.1 at s
            simp only [active,passive,place,Bool.false_eq_true,↓reduceIte] at hmean ⊢; simp only [qn,mul_div,← Finset.sum_div,← mul_assoc,← Finset.sum_mul,hmean]
          · change Split m' z.2 at s; simp only [active,passive,place,↓reduceIte] at hmean ⊢
            have rearrange (i : Fin m') : s.w i*((1-inner ℝ n (z.1 : Bloch))*(1-inner ℝ n (s.x i : Bloch))) =
                (1-inner ℝ n (z.1 : Bloch))*(s.w i*(1-inner ℝ n (s.x i : Bloch))) := by ring
            simp only [qn,mul_div,← Finset.sum_div,rearrange,← Finset.mul_sum,hmean]
        have conserve := affine qn qaffine R
        have pointwise (l : R.Leaves) : (tau r)^2/64*(if m l then 1 else 0) ≤ qn (R.endpoint l) := by
          cases hh : m l
          · simpa only [Bool.false_eq_true,↓reduceIte,mul_zero] using qpositive (R.endpoint l)
          · simpa only [↓reduceIte,mul_one] using qflat (R.endpoint l) (acc l hh)
        have hsuccess := mono R _ _ pointwise
        have scale : R.expect (fun l => (tau r)^2/64*(if m l then 1 else 0)) =
            (tau r)^2/64*successMass R m := by
          have hh := linear R (fun l => if m l then 1 else 0) (fun _ => 0) ((tau r)^2/64) 0
          simpa only [zero_mul,add_zero,successMass] using hh
        rw [scale,conserve] at hsuccess
        have na : inner ℝ n a = ‖a‖ := by
          simp only [n,real_inner_smul_left,real_inner_self_eq_norm_sq]
          field_simp [ane]
        have nb : ‖a‖*inner ℝ n b = inner ℝ a b := by
          simp only [n,real_inner_smul_left]
          field_simp [ane]
        let A := 1-‖a‖
        let B := 1-inner ℝ n b
        have An : 0 ≤ A := sub_nonneg.mpr an
        have Bn : 0 ≤ B := factor q.2
        have AB : A+‖a‖*B = 4*epsilon r := by dsimp [A,B]; nlinarith only [dot,nb]
        have ABn : 0 ≤ A*B := mul_nonneg An Bn
        have ABsq := congrArg (fun x : ℝ => x^2) AB
        have AM : ‖a‖*(A*B) ≤ 4*(epsilon r)^2 := by nlinarith only [ABsq,sq_nonneg (A-‖a‖*B)]
        have ABmul : (1/2)*(A*B) ≤ ‖a‖*(A*B) := mul_le_mul_of_nonneg_right ahalf.le ABn
        have qroot : qn q ≤ 8*(epsilon r)^2 := by
          have hq : qn q = A*B/4 := by dsimp [qn,A,B,a,b] at na ⊢; rw [na]
          rw [hq]; nlinarith only [AM,ABmul,sq_nonneg (epsilon r)]
        rw [tsq] at hsuccess
        have ssmall : successMass R m ≤ epsilon r := by
          have hm : epsilon r*successMass R m ≤ epsilon r*epsilon r := by nlinarith only [hsuccess,qroot]
          exact (mul_le_mul_iff_of_pos_left ep).mp hm
        have budget' := budgetAll q R m acc
        rw [hd] at budget'
        have hh := mul_le_mul_of_nonneg_left ssmall gp.le
        have heps := mul_le_mul_of_nonneg_right ghalf ep.le
        nlinarith only [budget',hh,heps]
      have deltaCut : failureDefect T mark = ∑ v, cut.mass v *
          failureDefect (cut.branch v).2 (fun l => mark (cut.include v l)) := by
        unfold failureDefect; rw [cutlaw cut]
        congr 1; funext v; simp_rw [cutEndpoint]
      have cutBound (v : cut.Nodes) :
          (if d (cut.branch v).1 = epsilon r ∧ Z r+tau r ≤ polarMoment (cut.branch v).1
            then cut.mass v else 0)*(epsilon r/2) ≤
            cut.mass v*failureDefect (cut.branch v).2 (fun l => mark (cut.include v l)) := by
        have nn : 0 ≤ failureDefect (cut.branch v).2 (fun l => mark (cut.include v l)) :=
          nonneg _ _ (fun l => by split_ifs; exact le_rfl; exact dn _)
        split_ifs with hh
        · exact mul_le_mul_of_nonneg_left
            (failAt (cut.branch v).1 (cut.branch v).2 (fun l => mark (cut.include v l))
              (fun l hm => by simpa only [cutEndpoint] using accepted (cut.include v l) hm) hh.1 hh.2)
            (cutNonneg cut v)
        · simpa only [zero_mul] using mul_nonneg (cutNonneg cut v) nn
      have deltaLower : frontierMass cut r (epsilon r) (tau r)*(epsilon r/2) ≤ failureDefect T mark := by
        rw [frontierMass,Finset.sum_mul,deltaCut]; exact Finset.sum_le_sum fun v _ => cutBound v
      have deltaN : 0 ≤ failureDefect T mark := nonneg T _ (fun l => by split_ifs; exact le_rfl; exact dn _)
      have zle : Z r ≤ g r := by
        have identity : g r-Z r = 1/(3*(1+kappa r)) := by
          unfold Z h g
          field_simp [ne_of_gt (by positivity : 0 < 1+kappa r)]; ring
        have hh : 0 ≤ g r-Z r := by rw [identity]; positivity
        linarith
      have ratio : Z r/g r ≤ 1 := (div_le_iff₀ gp).mpr (by simpa only [one_mul] using zle)
      have multiplied := mul_le_mul_of_nonneg_left wl ep.le
      have algebra : epsilon r*(H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark) =
          epsilon r*H r/2-(2*epsilon r*(Z r/g r)+1)*failureDefect T mark := by
        field_simp [ne_of_gt ep,ne_of_gt gp]
      rw [algebra] at multiplied
      have coeff : (3+2*epsilon r*(Z r/g r))*failureDefect T mark ≤ 4*failureDefect T mark := by
        apply mul_le_mul_of_nonneg_right _ deltaN
        have hh := mul_le_mul_of_nonneg_left ratio ep.le
        nlinarith
      have cubic : H r^3/65536 ≤ failureDefect T mark := by
        have hh : epsilon r*H r/8 ≤ failureDefect T mark := by nlinarith
        have identity : epsilon r*H r/8 = H r^3/65536 := by unfold epsilon; ring
        rwa [identity] at hh
      exact ⟨wl,by nlinarith [deltaLower],cubic⟩
  have kp : 0 < kappa r := by unfold kappa; positivity
  have kmin : 2/3 ≤ kappa r := by
    have hs := Real.sq_sqrt (show 0 ≤ 4+2*(r^2+(r^2)⁻¹) by positivity)
    have hn := Real.sqrt_nonneg (4+2*(r^2+(r^2)⁻¹))
    have hi : 0 ≤ (r^2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
    unfold kappa; nlinarith only [hs,hn,hi,sq_nonneg r]
  have kmax : kappa r < 1 := by
    have tp : 0 < r^2 := lt_trans (by norm_num) hlo
    have hprod := mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hhi)
    have hinv : r^2*(r^2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt tp)
    have hmult : r^2*(r^2+(r^2)⁻¹) < r^2*(5/2) := by nlinarith only [hprod,hinv]
    have hsum := (mul_lt_mul_iff_of_pos_left tp).mp hmult
    have hs := Real.sq_sqrt (show 0 ≤ 4+2*(r^2+(r^2)⁻¹) by positivity)
    have hn := Real.sqrt_nonneg (4+2*(r^2+(r^2)⁻¹))
    unfold kappa; nlinarith only [hs,hn,hsum]
  have hp : 0 < h r := by unfold h; positivity
  have hsmall : h r < 1/4 := by
    unfold h
    apply (div_lt_iff₀ (by positivity : 0 < 3*(1+kappa r))).mpr
    linarith only [kmin]
  have zn : 0 < Z r := by dsimp [Z]; linarith only [hsmall]
  have zmax : Z r ≤ 1 := by dsimp [Z]; linarith only [hp]
  have Hpos : 0 < H r := by unfold H; positivity
  have Hmax : H r ≤ 1 := by
    have hg : 0 ≤ 1-kappa r := sub_nonneg.mpr kmax.le
    have hh : Z r*(1-kappa r) ≤ 1 := by nlinarith only [zmax,zn,hg,kp]
    unfold H
    apply (div_le_iff₀ (by positivity : 0 < 2*kappa r)).mpr
    nlinarith only [hh,kmin]
  have ep : 0 < epsilon r := by unfold epsilon; positivity
  have eroot : epsilon r < d origin := by
    simp only [origin,d,defect,inner_zero_left]
    unfold epsilon; nlinarith only [Hpos,Hmax]
  have rewardExpect : ∀ {q : State} (R : Tree q) (u : State → ℝ),
      R.reward u = R.expect (fun l => u (R.endpoint l)) := by
    intro q R
    induction R with
    | stop => intro u; rfl
    | node actor q m s next ih => intro u; simp only [Tree.reward,Tree.expect,Tree.endpoint,ih]
  have scale : ∀ {q : State} (R : Tree q) (F : R.Leaves → ℝ) (c : ℝ),
      R.expect (fun l => c*F l) = c*R.expect F := by
    intro q R
    induction R with
    | stop => intros; rfl
    | node actor q m s next ih =>
      intro F c; simp only [Tree.expect,ih]
      simp_rw [← mul_assoc,mul_comm (s.w _) c,mul_assoc]
      rw [← Finset.mul_sum]
  have treeBound (P : Tree origin) :
      4*P.reward (terminal r) ≤ U r-H r^3/(49152*kappa r) := by
    let marking := fun l : P.Leaves =>
      if (((P.endpoint l).1 : Bloch),((P.endpoint l).2 : Bloch)) ∈ K_s r then true else false
    have accP (l : P.Leaves) (hl : marking l = true) :
        (((P.endpoint l).1 : Bloch),((P.endpoint l).2 : Bloch)) ∈ K_s r := by
      by_contra hh; simp [marking,hh] at hl
    -- Kleinmann, Kampermann and Bruss, arXiv:1105.5132v2, III.1
    -- (5a), (5b), (6) and III.2: pseudo-weak interpolation, copied recovery
    -- continuations and the first-threshold cut preserve the whole leaf law.
    -- The regular deviation is the minus marginal for gamma_-=P_-/4 and
    -- gamma_+=P_W/4, whose average state is I/4; on a product effect it is d.
    have refined :
      ∃ (T' : Tree origin) (pi : T'.Leaves → P.Leaves),
            T'.depth ≤ 2*P.depth ∧
            (∀ l, T'.endpoint l = P.endpoint (pi l)) ∧
            (∀ F : P.Leaves → ℝ, T'.expect (fun l => F (pi l)) = P.expect F) ∧
            ∃ cut : T'.Cut, ∀ v, 0 < cut.mass v →
              d (cut.branch v).1 = epsilon r ∨
                (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0) := by
      let epsilon := epsilon r
      let alpha {z : State} {m : ℕ} (actor : Bool) (s : Split m (active actor z))
          (epsilon : ℝ) (i : Fin m) : ℝ :=
        s.w i * max (epsilon - d (place actor (s.x i) (passive actor z))) 0 / (d z - epsilon)
      let beta {z : State} {m : ℕ} (actor : Bool) (s : Split m (active actor z))
          (epsilon : ℝ) : ℝ := 1 / (1 + ∑ i, alpha actor s epsilon i)
      suffices ∀ (z : State) (T : Tree z), epsilon < d z →
        ∃ (T' : Tree z) (pi : T'.Leaves → T.Leaves),
              T'.depth ≤ 2*T.depth ∧
              (∀ l, T'.endpoint l = T.endpoint (pi l)) ∧
              (∀ F : T.Leaves → ℝ, T'.expect (fun l => F (pi l)) = T.expect F) ∧
              ∃ cut : T'.Cut, ∀ v, 0 < cut.mass v →
                d (cut.branch v).1 = epsilon ∨
                  (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0) by
        exact this origin P eroot
      intro z T hz
      have dz (actor : Bool) (a b : Ball) :
          d (place actor a b) = (1-inner ℝ (a : Bloch) (b : Bloch))/4 := by
        cases actor
        · rfl
        · simp only [d,place,↓reduceIte,defect,real_inner_comm (a : Bloch) (b : Bloch)]
      have affine (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z)) :
          (∑ i, s.w i * d (place actor (s.x i) (passive actor z))) = d z := by
        have hi : (∑ i, s.w i * inner ℝ (s.x i : Bloch) (passive actor z : Bloch)) =
            inner ℝ (active actor z : Bloch) (passive actor z : Bloch) := by
          rw [← s.mean,sum_inner]
          simp_rw [real_inner_smul_left]
        simp_rw [dz,mul_div,mul_sub,mul_one,← Finset.sum_div,Finset.sum_sub_distrib]
        rw [s.total,hi]
        cases actor
        · rfl
        · simp only [d,active,passive,↓reduceIte,defect,real_inner_comm (z.1 : Bloch) (z.2 : Bloch)]
      have rows (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z))
          (hz : epsilon < d z) :
          ∃ (row : Split m (active actor z))
            (col : ∀ i, Split m (row.x i)),
            (∀ i j, (col i).x j = s.x j) ∧
            (∀ i, row.w i = beta actor s epsilon * (s.w i + alpha actor s epsilon i)) ∧
            (∀ i j, row.w i * (col i).w j = beta actor s epsilon *
              ((if i = j then 1 else 0) + alpha actor s epsilon i) * s.w j) ∧
            (∀ j, (∑ i, row.w i * (col i).w j) = s.w j) ∧
            (∀ i, 0 < row.w i →
              d (place actor (row.x i) (passive actor z)) =
                max epsilon (d (place actor (s.x i) (passive actor z)))) ∧
            (∀ i, epsilon < d (place actor (row.x i) (passive actor z)) →
              0 < row.w i → row.x i = s.x i ∧
                (∀ j, (col i).w j = if i = j then 1 else 0)) ∧
            (∀ i, row.w i = 0 → row.x i = s.x i ∧
              (∀ j, (col i).w j = if i = j then 1 else 0)) := by
        let A := alpha actor s epsilon
        let B := beta actor s epsilon
        let den := fun i => s.w i + A i
        have hd : 0 < d z - epsilon := sub_pos.mpr hz
        have hA (i : Fin m) : 0 ≤ A i :=
          div_nonneg (mul_nonneg (s.nonneg i) (le_max_right _ _)) hd.le
        have hden (i : Fin m) : 0 ≤ den i := add_nonneg (s.nonneg i) (hA i)
        have hsA : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
        have hBd : 0 < 1 + ∑ i, A i := by linarith
        have hB : 0 < B := one_div_pos.mpr hBd
        have Bcancel : B * (1+∑ i, A i) = 1 := one_div_mul_cancel (ne_of_gt hBd)
        let c := fun i j => if 0 < den i then
          ((if i = j then 1 else 0) + A i) * s.w j / den i else if i = j then 1 else 0
        have cn (i j : Fin m) : 0 ≤ c i j := by
          dsimp [c]
          split_ifs
          · exact div_nonneg (mul_nonneg (add_nonneg (by norm_num) (hA i)) (s.nonneg j)) (hden i)
          · exact div_nonneg (mul_nonneg (add_nonneg (by norm_num) (hA i)) (s.nonneg j)) (hden i)
          · norm_num
          · norm_num
        have ct (i : Fin m) : ∑ j, c i j = 1 := by
          by_cases hpos : 0 < den i
          · simp only [c,if_pos hpos]; rw [← Finset.sum_div]
            have hnum : (∑ j, ((if i = j then 1 else 0)+A i)*s.w j) = den i := by
              simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum,s.total,mul_one,
                ite_mul,one_mul,zero_mul]
              simp [den]
            rw [hnum,div_self (ne_of_gt hpos)]
          · simp [c,hpos]
        let X : Fin m → Ball := fun i => ⟨∑ j, c i j • (s.x j : Bloch),
          (convex_closedBall (0 : Bloch) 1).sum_mem (fun j _ => cn i j) (ct i)
            (fun j _ => (s.x j).property)⟩
        have Xzero (i : Fin m) (hzero : den i = 0) : X i = s.x i := by
          apply Subtype.ext
          change (∑ j, c i j • (s.x j : Bloch)) = (s.x i : Bloch); simp [c,hzero]
        have joint (i j : Fin m) : B * den i * c i j =
            B * ((if i = j then 1 else 0) + A i) * s.w j := by
          by_cases hpos : 0 < den i
          · dsimp [c]; rw [if_pos hpos]; field_simp [ne_of_gt hpos] <;> ring
          · have hzero : den i = 0 := le_antisymm (le_of_not_gt hpos) (hden i)
            have hwzero : s.w i = 0 := by dsimp [den] at hzero; linarith [s.nonneg i,hA i]
            have hAzero : A i = 0 := by dsimp [den] at hzero; linarith [s.nonneg i,hA i]
            rw [hzero,hAzero]
            by_cases hij : i = j
            · subst j; simp [hwzero]
            · simp [hij]
        have column (j : Fin m) : (∑ i, B * den i * c i j) = s.w j := by
          simp_rw [joint]
          rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib]
          have hdelta : (∑ i : Fin m, if i = j then (1 : ℝ) else 0) = 1 := by simp
          rw [hdelta]; rw [Bcancel,one_mul]
        have rtotal : ∑ i, B * den i = 1 := by
          dsimp [den]; rw [← Finset.mul_sum,Finset.sum_add_distrib,s.total]; exact Bcancel
        have rmean : (∑ i, (B * den i) • (X i : Bloch)) = (active actor z : Bloch) := by
          change (∑ i, (B * den i) • ∑ j, c i j • (s.x j : Bloch)) = _
          simp_rw [Finset.smul_sum,← mul_smul]
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_smul,column]
          exact s.mean
        let row : Split m (active actor z) :=
          ⟨fun i => B*den i,X,fun i => mul_nonneg hB.le (hden i),rtotal,rmean⟩
        let col : ∀ i, Split m (row.x i) := fun i => ⟨c i,s.x,cn i,ct i,rfl⟩
        have row_defect (i : Fin m) (hpos : 0 < row.w i) :
            d (place actor (row.x i) (passive actor z)) =
              max epsilon (d (place actor (s.x i) (passive actor z))) := by
          change 0 < B * den i at hpos
          have hpos' : 0 < den i := (mul_pos_iff_of_pos_left hB).mp hpos
          have hf : (∑ j, c i j * d (place actor (s.x j) (passive actor z))) =
              d (place actor (row.x i) (passive actor z)) := by
            simp_rw [dz,mul_div,mul_sub,mul_one,← Finset.sum_div,Finset.sum_sub_distrib]
            rw [ct i]
            congr 2
            change (∑ j, c i j * inner ℝ (s.x j : Bloch) (passive actor z : Bloch)) =
              inner ℝ (∑ j, c i j • (s.x j : Bloch)) (passive actor z : Bloch)
            rw [sum_inner]; simp only [real_inner_smul_left]
          have hform : d (place actor (row.x i) (passive actor z)) =
              (s.w i * d (place actor (s.x i) (passive actor z)) + A i * d z)/den i := by
            rw [← hf]
            change (∑ j, c i j * d (place actor (s.x j) (passive actor z))) = _; simp only [c,if_pos hpos']
            simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
            have hnume : (∑ j, (((if i = j then 1 else 0)+A i)*s.w j) *
                d (place actor (s.x j) (passive actor z))) =
                s.w i*d (place actor (s.x i) (passive actor z))+A i*d z := by
              simp_rw [add_mul,Finset.sum_add_distrib]
              simp only [ite_mul,one_mul,zero_mul]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum,affine actor z m s]
            rw [hnume]
          rw [hform]
          by_cases hlow : d (place actor (s.x i) (passive actor z)) < epsilon
          · rw [max_eq_left hlow.le]
            apply (div_eq_iff (ne_of_gt hpos')).mpr
            have halpha : A i * (d z-epsilon) = s.w i*(epsilon-d (place actor (s.x i) (passive actor z))) := by
              dsimp [A,alpha]; rw [max_eq_left (by linarith : 0 ≤ epsilon-d (place actor (s.x i) (passive actor z)))]; exact div_mul_cancel₀ _ (ne_of_gt hd)
            dsimp [den]; nlinarith [halpha]
          · have ha0 : A i = 0 := by
              dsimp [A,alpha]; rw [max_eq_right (by linarith : epsilon-d (place actor (s.x i) (passive actor z)) ≤ 0)]
              simp
            rw [max_eq_right (le_of_not_gt hlow),ha0]
            have hwi : s.w i ≠ 0 := by simpa only [den,ha0,add_zero] using ne_of_gt hpos'
            simp [den,ha0,hwi]
        refine ⟨row,col,fun _ _ => rfl,fun _ => rfl,joint,column,row_defect,?_,?_⟩
        · intro i habove hpos
          have hdi : epsilon < d (place actor (s.x i) (passive actor z)) := by
            rw [row_defect i hpos] at habove; exact (lt_max_iff.mp habove).resolve_left (lt_irrefl epsilon)
          have ha0 : A i = 0 := by
            dsimp [A,alpha]; rw [max_eq_right (by linarith : epsilon-d (place actor (s.x i) (passive actor z)) ≤ 0)]
            simp
          have hwpos : 0 < s.w i := by
            change 0 < B * den i at hpos
            have hh : 0 < den i := (mul_pos_iff_of_pos_left hB).mp hpos
            simpa only [den,ha0,add_zero] using hh
          have hcdiag (j : Fin m) : c i j = if i = j then 1 else 0 := by
            dsimp [c]; rw [if_pos (by simpa only [den,ha0,add_zero] using hwpos),ha0,add_zero]
            by_cases hij : i = j
            · subst j; simp [den,ha0,ne_of_gt hwpos]
            · simp [hij]
          refine ⟨?_,hcdiag⟩
          apply Subtype.ext
          change (∑ j, c i j • (s.x j : Bloch)) = (s.x i : Bloch); simp [hcdiag]
        · intro i hzero
          have hzden : den i = 0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hB)
          refine ⟨Xzero i hzden,?_⟩
          intro j
          change c i j = _; simp only [c,hzden,lt_self_iff_false,if_false]
      revert hz
      induction T with
      | stop z =>
        intro hz
        refine ⟨Tree.stop z,id,by simp [Tree.depth],fun _ => rfl,fun _ => rfl,
          Tree.Cut.here (Tree.stop z),?_⟩
        intro v _; exact Or.inr ⟨hz,rfl⟩
      | node actor z m s next ih =>
        intro hz
        obtain ⟨row,col,hx,hr,hjoint,hcolumn,hthreshold,habove,hzero⟩ := rows actor z m s hz
        let M := Finset.univ.sup (fun i => (next i).depth)
        have depth_child (i : Fin m) : (next i).depth ≤ M := Finset.le_sup (f := fun i => (next i).depth) (Finset.mem_univ i)
        have rowCertificate (i : Fin m) :
            ∃ (R : Tree (place actor (row.x i) (passive actor z)))
              (pi : R.Leaves → (j : Fin m) × (next j).Leaves),
              R.depth ≤ 2*M+1 ∧
              (∀ l, R.endpoint l = (next (pi l).1).endpoint (pi l).2) ∧
              (∀ F : ((j : Fin m) × (next j).Leaves) → ℝ,
                R.expect (fun l => F (pi l)) =
                  ∑ j, (col i).w j * (next j).expect (fun l => F ⟨j,l⟩)) ∧
              ∃ cut : R.Cut, ∀ v, 0 < row.w i * cut.mass v →
                d (cut.branch v).1 = epsilon ∨
                  (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0) := by
          by_cases hri : row.w i = 0
          · have hxi := (hzero i hri).1
            have hc := (hzero i hri).2
            have hstate := congrArg (fun x => place actor x (passive actor z)) hxi
            rw [hstate]
            refine ⟨next i,fun l => ⟨i,l⟩,?_,fun _ => rfl,?_,Tree.Cut.here (next i),?_⟩
            · have hh := depth_child i; omega
            · intro F; simp [hc]
            · intro v hpos; rw [hri,zero_mul] at hpos; exact (lt_irrefl _ hpos).elim
          · have hri' : 0 < row.w i := lt_of_le_of_ne (row.nonneg i) (Ne.symm hri)
            by_cases had : epsilon < d (place actor (row.x i) (passive actor z))
            · have hxi := (habove i had hri').1
              have hc := (habove i had hri').2
              have hchild : epsilon < d (place actor (s.x i) (passive actor z)) := by rwa [hxi] at had
              obtain ⟨R,pi,hd,hep,hlaw,cut,hcut⟩ := ih i hchild
              have hstate := congrArg (fun x => place actor x (passive actor z)) hxi
              rw [hstate]
              refine ⟨R,fun l => ⟨i,pi l⟩,?_,hep,?_,cut,?_⟩
              · have hh := depth_child i; omega
              · intro F; simp only [hc,ite_mul,one_mul,zero_mul]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]; exact hlaw (fun l => F ⟨i,l⟩)
              · intro v hpos
                have hv : 0 < cut.mass v := by
                  by_contra hh
                  have hn := mul_nonpos_of_nonneg_of_nonpos (row.nonneg i) (le_of_not_gt hh)
                  linarith
                exact hcut v hv
            · have hdrow : d (place actor (row.x i) (passive actor z)) = epsilon := by
                have hh := hthreshold i hri'
                have hlow := le_of_not_gt had
                have hhigh := (le_max_left epsilon _).trans hh.symm.le
                exact le_antisymm hlow hhigh
              let recovery : Split m (row.x i) :=
                ⟨(col i).w,s.x,(col i).nonneg,(col i).total,
                  by simpa only [hx] using (col i).mean⟩
              cases actor
              · let R := Tree.node false (place false (row.x i) (passive false z)) m recovery next
                refine ⟨R,fun l => ⟨l.1,l.2⟩,?_,fun _ => rfl,fun _ => rfl,Tree.Cut.here R,?_⟩
                · change 1+M ≤ 2*M+1; omega
                · intro v _; exact Or.inl hdrow
              · let R := Tree.node true (place true (row.x i) (passive true z)) m recovery next
                refine ⟨R,fun l => ⟨l.1,l.2⟩,?_,fun _ => rfl,fun _ => rfl,Tree.Cut.here R,?_⟩
                · change 1+M ≤ 2*M+1; omega
                · intro v _; exact Or.inl hdrow
        choose R pi hd hep hlaw cut hcut using rowCertificate
        let T' := Tree.node actor z m row R
        refine ⟨T',fun l => pi l.1 l.2,?_,?_,?_,Tree.Cut.descend actor z m row R cut,?_⟩
        · have hh : Finset.univ.sup (fun i => (R i).depth) ≤ 2*M+1 :=
            Finset.sup_le fun i _ => hd i
          change 1 + Finset.univ.sup (fun i => (R i).depth) ≤ 2*(1+M)
          omega
        · intro l; exact hep l.1 l.2
        · intro F
          change ((j : Fin m) × (next j).Leaves) → ℝ at F
          change (∑ i, row.w i * (R i).expect (fun l => F (pi i l))) =
            ∑ j, s.w j * (next j).expect (fun l => F ⟨j,l⟩)
          simp_rw [hlaw,Finset.mul_sum,← mul_assoc]
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_mul,hcolumn]
        · intro v hpos; exact hcut v.1 v.2 hpos
    obtain ⟨R,pi,depth,hep,law,cut,hcut⟩ := refined
    let markingR := fun l : R.Leaves => marking (pi l)
    have accR (l : R.Leaves) (hl : markingR l = true) :
        (((R.endpoint l).1 : Bloch),((R.endpoint l).2 : Bloch)) ∈ K_s r := by
      simpa only [hep] using accP (pi l) hl
    rcases certificateAll origin R markingR accR with ⟨dn,budget,excess,cutdelta,variance,precursor,quant⟩
    have cubic := (quant cut hcut rfl).2.2
    have eqReward : P.reward (terminal r) = h r*successMass R markingR := by
      rw [rewardExpect]
      have eqlaw := law (fun l => terminal r (P.endpoint l))
      simp only [← hep] at eqlaw; rw [← eqlaw]
      have point : (fun l => terminal r (R.endpoint l)) =
          (fun l => h r*(if markingR l then 1 else 0)) := by
        funext l
        by_cases hh : (((P.endpoint (pi l)).1 : Bloch),((P.endpoint (pi l)).2 : Bloch)) ∈ K_s r
        · simp [terminal,hep,markingR,marking,hh]
        · simp [terminal,hep,markingR,marking,hh]
      rw [point,scale]; rfl
    have rootDef : d origin = 1/4 := by simp [origin,d,defect]
    rw [rootDef] at budget
    have denominator : 0 < 1+kappa r := by positivity
    have probability : 4*h r*successMass R markingR =
        (1-4*failureDefect R markingR)/(3*kappa r) := by
      unfold g at budget
      unfold h
      field_simp [ne_of_gt kp,ne_of_gt denominator] at budget ⊢
      nlinarith only [budget]
    have target : U r-H r^3/(49152*kappa r) =
        (1-4*(H r^3/65536))/(3*kappa r) := by
      unfold U
      field_simp [ne_of_gt kp] <;> ring
    rw [eqReward,← mul_assoc,probability,target]; exact div_le_div_of_nonneg_right (by linarith only [cubic]) (by positivity)
  have valueBound : 4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) := by
    have hv := (source_bellman_finite_tree_identity r hr hlo hhi).2.2.2.2.2.1 origin
    have bound : treeValue r origin ≤ (U r-H r^3/(49152*kappa r))/4 := by
      apply csSup_le
      · exact ⟨(Tree.stop origin).reward (terminal r),Tree.stop origin,rfl⟩
      · rintro _ ⟨P,rfl⟩; linarith only [treeBound P]
    rw [hv.1]; linarith only [bound]
  have strict : U r-H r^3/(49152*kappa r) < U r := by
    have hg : 0 < H r^3/(49152*kappa r) := by positivity
    linarith only [hg]
  have sepRoot : fSEP r origin = U r/4 := by simp [fSEP,origin,defect,U] <;> ring
  have psiGap : H r^3/(196608*kappa r) ≤ psi r origin := by
    unfold psi; rw [sepRoot]
    have identity : H r^3/(196608*kappa r) = (H r^3/(49152*kappa r))/4 := by ring
    rw [identity]; linarith only [valueBound]
  exact ⟨certificateAll z T mark accepted,valueBound,strict,psiGap⟩
end D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
