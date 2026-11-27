/- GID: D5/S3/Zeros/GRH/New/Exchange/GridMove
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/GridMove
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.GridMove. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/GridMove.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.PairTensorData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Part of: Crude rows: integral twisted lifts and bounded conjugates (see New.Exchange.CrudeRows).

This file: Tuples of matrices, tidy data on paths, and the periods of the staircase. Weights,
levels, kernels and final period along the definite edges of the grids. -/

noncomputable section

open BigOperators Finset Fintype Function Matrix

variable {P} {D' : Data P} (ϑ : D'.MFoldTwist) {ϑ' : D'.MFoldTwist} (g :
  ∀ p, GL (D'.NodeIndex p) (Data.gridModulus ϑ').ResRing) (n : ℕ)

namespace Data

/-- Tuples: for each ordered pair of nodes (P, P′), a matrix over the residue ring of
`Data.gridModulus`, columns indexed by the basis of P, rows by that of P′. -/
abbrev EdgeTuple := ∀ e : _ × _,
  Matrix (D'.NodeIndex e.2) (D'.NodeIndex e.1) (gridModulus ϑ).ResRing

/-- Data: complex linear functionals on the space of complex functions of tuples of matrices
(`Data.EdgeTuple`). -/
abbrev GridDatum := (EdgeTuple ϑ → ℂ) →ₗ[ℂ] ℂ

/-- The μ-edges from p to q (those whose character `Data.edgeChar` carries the twist): the first
index changes if p lies in the grid Z, and stays if p lies in the grid V. -/
abbrev IsMuEdge (p q : Node) := p.1 ↔ p.2.1 ≠ q.2.1

/-- The character modulo 𝔪 of an edge: local components (ω_wϑ_w)^l on μ-edges (`Data.IsMuEdge`),
else ω_w^l; l − 1 is the source's second index if the first indices agree, else its first. -/
def edgeChar (e : _ × _) := (gridModulus ϑ).charOfTamePart
  (gridTamePart ϑ (IsMuEdge e.1 e.2) (ite (e.1.2.1 = e.2.2.1) e.1.2.2 e.1.2.1))

/-- The family g lies in the level `Data.nodeLevel` at the node (0, m) of both grids, and at (a, a)
its value in Z is its value in V extended by 1. -/
def IsAdmissibleFamily {D : Data P} {ϑ : D.MFoldTwist} (g :
  ∀ p, GL (D.NodeIndex p) (gridModulus ϑ).ResRing) := (∀ z, g (z, 0, D.m) ∈ nodeLevel ..) ∧
  ∀ a, g (_, a, a) = blockInlGL (D.gridDiagEquiv a) (g (_, a, a))

/-- The tuple S moved by g: on an edge from P to P′ the matrix x becomes g_{P′}⁻¹ x g_P. -/
def tupleAction (S : EdgeTuple ϑ') (e : Node × Node) := (g e.2)⁻¹.1 * S e * (g e.1).1

/-- The product over the edges e in w of the character `Data.edgeChar` of e at det g(target)/det
g(source). -/
def edgeCharProd (w : Finset (Node × Node)) : ℂ := ∏ e ∈ w,
  (edgeChar ϑ' e).toUnitHom ((g e.2).det / (g e.1).det)

/-- The number |R|^((2n_m)²), R the residue ring of `Data.gridModulus`; used as a bound for the
number of matrices on an edge. -/
abbrev tupleBound := card (D'.gridModulus ϑ).ResRing ^ (2 * D'.n D'.m) ^ 2

/-- For every pair of nodes in w that is a μ-edge (`Data.IsMuEdge`), the matrix of the tuple S at
that pair has a left inverse over O_E/𝔪. -/
abbrev LeftInvOnMuEdges (S : EdgeTuple ϑ') (w : Finset (Node × Node)) := ∀ e ∈ w, IsMuEdge e.1 e.2 →
  HasLeftInv (S e)

/-- Λ is a combination of at most `Data.tupleBound`^n point evaluations, each non-zero coefficient a
root of unity at a tuple with left invertible matrices on the μ-edges in w. -/
def IsShortSum (w : Finset (Node × Node)) (Λ : GridDatum ϑ') := ∃ X : Type, ∃ W,
  ∃ (c : X → ℂ) (s : X → _), #W ≤ tupleBound ϑ' ^ n ∧
  (∀ x, c x ≠ 0 → IsOfFinOrder (c x) ∧ LeftInvOnMuEdges (s x) w) ∧ ∀ f, Λ f = ∑ x ∈ W, c x * f (s x)

/-- The datum f ↦ Λ(S ↦ ∑_x κ(S, x) f(t(S, x))): each tuple S is replaced by the tuples t(S, x)
with weights κ(S, x). -/
abbrev GridDatum.bind {D : Data P} {ϑ : D.MFoldTwist} (Λ : GridDatum ϑ) {X : Type} [Fintype X] (κ :
  _ → X → ℂ) (t : _ → X → _) := (Λ ∘ₗ .pi fun S ↦ ∑ x, κ S x • .proj (t S x) : GridDatum ϑ)

/-- Tidy data of order n for the edges w: admissible families g (`Data.IsAdmissibleFamily`) multiply
Λ by `Data.edgeCharProd` g w, and Λ is a short sum (`Data.IsShortSum`). -/
structure IsTidy {D : Data P} {ϑ : D.MFoldTwist} (n : ℕ) (w : Finset (Node × Node)) (Λ :
  GridDatum ϑ) where
  equivariant g : IsAdmissibleFamily g → ∀ f, Λ (f <| tupleAction g ·) = edgeCharProd g w * Λ f
  isShortSum : IsShortSum n w Λ

/-- Λ is a short sum (`Data.IsShortSum`), and each family g lying in the levels at the nodes (0,
i), i ≤ m, of both grids multiplies Λ by `Data.edgeCharProd` g w. -/
def IsLevelTidy (w : Finset (Node × Node)) (Λ : GridDatum ϑ') := IsShortSum n w Λ ∧ ∀ g, (∀ z, ∀ i ≤
  D'.m, g (z, 0, i) ∈ nodeLevel ..) → ∀ f, Λ (f <| tupleAction g ·) = edgeCharProd g w * Λ f

/-- The edge of grid z from the node (a, b) to the node (a, b+1), as an ordered pair of nodes. -/
abbrev verticalEdge (z : Bool) (a b : ℕ) := ((z, a, b), z, a, b + 1)

/-- The ordered pair of grid nodes (`Data.Node`) from (z, a, b) to (z, a + 1, b): the edge
that raises the index a by one. -/
abbrev rowEdge (z : Bool) (a b : ℕ) := ((z, a, b), z, a + 1, b)

/-- The set of edges from (0, i) to (0, i + 1) in grid z, for b ≤ i < m. -/
def legEdges (z : Bool) (b : ℕ) := (Ico b D'.m).image (verticalEdge z 0)

/-- The edges of a path in grid z: (0, j) → (0, j+1) for b ≤ j < m, and (i, b) → (i+1, b) for i
< a. -/
def gridPath (z : Bool) (a b : ℕ) := (range a).image (rowEdge z · b) ∪ D'.legEdges z b

/-- The edges of the path of stage n: in both grids, those from (0, n) to (n, n) and those from (0,
n) to (0, m). -/
abbrev path := D'.gridPath false n n ∪ D'.gridPath true n n

variable {P : Parameters} {D : Data P} {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) (z : Bool) (b : ℕ) in
/-- The composite of the descents `Data.descentMove` from node (0, m) to node (0, b) of grid z, each
with the matrix that S puts on its edge; zero for b > m. -/
def legDescents b : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b := if b < D.m then descentMove (S
  (verticalEdge ..)) ∘ₗ legDescents _ else
  Pi.single (M := (D.GridForm .. →ₗ[ℂ] D.GridForm z 0 ·)) _ .id b

variable {D : Data P} {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) (z : Bool) {j} (ϑ₁ : D.MFoldTwist) (w :
  Finset (Node × Node))

/-- The map on forms from node (0, m) to node (a, b) of grid z: descend to (0, b), then lift a
times, using the matrices S puts on the edges. -/
def gridPathMap : ∀ a b, D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z a b
  | 0, _ => legDescents S .. | _ + 1, _ => liftMove (S (rowEdge ..)) ∘ₗ gridPathMap ..

/-- The bilinear period (f, F) ↦ ∫ f(x) F((x ⊕ u^j)g) dx over [U(V_{j,j})], for a real point g and
u = `Modulus.flipScalar` of `Data.gridModulus`. -/
@[simp] def diagonalPeriodForm h g := (Space.periodPairing (isConjKernelPair_gridKernel ⟨h, h⟩) ⟨1,
  ⟨fun x ↦ .reindex (D.gridDiagEquiv j) _ (.sum (x, 1, (gridModulus ϑ₁).flipScalar ^ j)), by
  fun_prop⟩, ⟨1, 0, by simp⟩, _, fun _ ↦ gridSpace_diag h ▸ (Space.height_reindex ..).trans_le
  (Space.height_sum_le ..)⟩ g : D.GridForm .. →ₗ[ℂ] GridForm .. →ₗ[ℂ] ℂ)

/-- The stage j period of y = (ϑ, Ξ, φ): Λ(ϑ) of S ↦ `Data.diagonalPeriodForm` of NΞ and φ,
descended to (0, j), lifted to (j, j) with data S; N = `Data.levelIndex` at Y_m. -/
@[simp] def gridPeriod (Λ : ∀ ϑ, D.GridDatum ϑ) (y : _ × _ × _) h g := Λ y.1 fun S ↦
  diagonalPeriodForm y.1 h g
  (gridPathMap S _ j j (levelIndex y.1 false 0 D.m • y.2.1)) (gridPathMap S _ j j y.2.2)

lemma edgeCharProd_mul g' : edgeCharProd (g * g') w =
  edgeCharProd g w * edgeCharProd g' w := by simp [edgeCharProd, field]

variable (S' : EdgeTuple ϑ) (z : Bool) (b a b' : ℕ) {j : ℕ}

lemma legDescents_congr (h : ∀ e ∈ D.legEdges z b, S e = S' e) : legDescents S z b =
  legDescents S' z b := by fun_induction legDescents S z b <;> grind [legEdges, legDescents]

lemma gridPathMap_congr (h : ∀ e ∈ D.gridPath z a b', S e = S' e) : gridPathMap S z a b' =
  gridPathMap S' z a b' := by induction a <;> grind [gridPath, gridPathMap, legDescents_congr]

/-- Let |X| ≤ q^k, q = `Data.tupleBound` ϑ; for S satisfying `Data.LeftInvOnMuEdges` on w, let each
κ(S, x) ≠ 0 be a root of unity with t(S, x) satisfying it on w'. If Λ satisfies `Data.IsShortSum` n
w, then `Data.GridDatum.bind` Λ κ t satisfies `Data.IsShortSum` (n + k) w'. -/
lemma IsShortSum.bind {n k w w' X} [Fintype X] {κ : _ → X → ℂ} {t} {Λ : GridDatum ϑ} (N : card X ≤
  tupleBound ϑ ^ k) (H : ∀ S x, κ S x ≠ 0 → LeftInvOnMuEdges S w → IsOfFinOrder (κ S x) ∧
  LeftInvOnMuEdges (t S x) w') : IsShortSum n w Λ → IsShortSum
  (n + k) w' (Λ.bind κ t) | ⟨_, W, c, s, h⟩ => ⟨_, W ×ˢ ⊤, (c • κ ∘ s).uncurry, (t ∘
  s).uncurry, by simp [pow_add, mul_le_mul', sum_product, mul_sum, *]; grind [IsOfFinOrder.mul]⟩

lemma card_matrix_le_tupleBound {p q} (h : p.2 ≤ (D.m, D.m)) (h' : q.2 ≤ (D.m, D.m)) :
    card (Matrix (D.NodeIndex p) (D.NodeIndex q) (gridModulus ϑ).ResRing) ≤ tupleBound ϑ := by
  erw [card_fun, card_fun, ← pow_mul, tupleBound, sq]
  gcongr <;> apply_rules [Fintype.card_pos, card_gridIndex_le]

/-- The index set of the node (j, m) of grid z; these nodes carry the chain of lifts between
definite groups. -/
abbrev EndIndex := D.GridIndex z a D.m

/-- There are column multiplicities κ and exponents e_j with (κ, e_j) going up (`IsLiftWeight`) from
node (j, m) to (j+1, m) along the weight `Data.gridWeight` at the larger rank, e_{j+1} that at
the smaller, and (κ, e_j) of parameter −`Data.gridParam` at (j, m), j ≤ m. -/
def endWeightData : let ι := D.EndIndex z; Σ' κ, Σ' e : ℕ → _, (∀ j,
    IsLiftWeight (ι j) (ι (j + 1)) κ (D.gridWeight z j (ι (j + 1))) (e j) ∧ D.gridWeight z j (ι j) =
    e (j + 1)) ∧ ∀ j ≤ D.m, IsHCParam κ (e j) (-D.gridParam z 0 j D.m) := by
  intro ι; have hp j h := D.paramsCorrespond_grid true z 0 j _ rfl h .refl
  have s :=
    @strictMono_nat_of_lt_succ _ _ (Fintype.card <| ι ·) (by simp [ι, card_gridIndex, D.t_odd.pos])
  choose κ H using exists_isHCParam_of_le (e := D.gridWeight z 0 (ι 1)) (fun _ ↦
    (Set.range (Fintype.card <| ι ·)).indicator fun _ ↦ D.h - D.t - z.toNat)
    (D.hasGap_gridParam · z 0 D.m |>.neg) (hp 0 D.nat_le_of_hasLogBound · |>.rec (by
    simp [IsMatchedPair, pairSign, gridSigns_eq_one]; grind-ring -linarith -ac -order))
  refine ⟨κ, _, (⟨·, Nat.rec (fun _ ↦ H.1) (by grind [IsHCParam.paramsCorrespond_iff,
    gridSigns_eq_one])⟩) fun j ↦ .imp_left (⟨·, s (by simp), rfl⟩) ?_⟩
  simp +contextual [ι, H, FitsRanks, s.monotone.ne_of_lt_of_lt_nat j, funext_iff, s _, (s.monotone
    j.zero_le).trans_lt]; cases z <;> simp [gridWeight, card_gridIndex] <;> grind

/-- The determinant exponents e_j that complete κ = `Data.endWeightData` to the weight at the node
(j, m) of grid z. -/
abbrev endDetExp := (D.endWeightData z).2.1

/-- The level at node (j, m) of grid z: the elements of K₀ whose reduction modulo `Data.gridModulus`
lies in the subgroup `Data.nodeLevel` of that node. -/
def endLevel :=
  (gridModulus ϑ₁).levelOfSubgroup (n := EndIndex z b') (nodeLevel ϑ₁ (z, b', D.m)) deriving IsLevel

lemma endLevel_le_principalLevel : endLevel ϑ₁ z b' ≤ principalLevel _ gridLevelGen :=
  fun _ ⟨_, k, a⟩ ↦ a ▸ (Modulus.mem_principalLevel_iff gridModulus_one_ideal _).2
  ((Units.ext (Modulus.factor_reductionK₀ ..)).symm.trans
  (((ite_le_sup ..).trans_eq (bot_sup_eq _) : nodeLevel .. ≤ _) k))

/-- The theta kernel of weight `Data.endWeightData` and scale per from the node (j, m) to (j+1, m)
of grid z, between algebraic forms of the levels `Data.endLevel`; per = `Parameters.jetScale`. -/
def endKernel := have h := (endWeightData z).2.2.1 b'; thetaKernel h.1 (1 * P.jetScale D.s)
       (h.2 ▸ gridChar_hasWeight ϑ₁ ..) (gridChar_hasWeight ϑ₁ ..) (endLevel ϑ₁ z b')

lemma boxes_endWeightData_le (h : j ≤ D.m) : Fintype.card (D.EndIndex z j) ≤ 2 * D.n D.m ∧
  boxes (D.endWeightData z).1 (Fintype.card (D.EndIndex z j)) ≤ D.b₁ * D.r ^ 4 ∧ ∀ τ,
  (D.endDetExp z j τ).natAbs ≤ ⌈20 * D.b⌉₊ := by
  have := boxes_le_of_isHCParam ((D.endWeightData z).2.2.2 j h) (by simpa using
    (D.abs_gridParam_le · h le_rfl))
  grw [this.1, card_gridIndex_le] <;> simp [h, this]; exact D.nat_le_of_hasLogBound

/-- The branching matrix: the chosen integer matrix that pairs the weights at the nodes (m, m)
of the grids V and Z. -/
def endBranching := Classical.indefiniteDescription _
  (exists_branching_pairing (D.gridDiagEquiv_spec le_rfl) (D.gridSigns_eq_one le_rfl)
  ((D.endWeightData _).2.2.2 _ le_rfl) ((D.endWeightData _).2.2.2 _ le_rfl) D.gridParam_interlace)

/-- The complex bilinear form (v′, v) ↦ v′ᵀBv of the branching matrix B = `Data.endBranching`. -/
abbrev endPairing := (dotProductBilin ℂ ℂ).compl₂ (D.endBranching.1.map (↑)).mulVecLin

def endBlockPoint h := U.block (D.gridDiagEquiv D.m) (h, (gridModulus ϑ₁).flipScalar ^ D.m)

instance isStd_gridSpace {z i} : (D.gridSpace 0 z i D.m).IsStd := by cases z <;> cases i <;> first
  | apply isStd_spaceY | exact D.m_eq_two_mul_varrho_add_two ▸ isStd_signedSpace (gridSigns_eq_one _
    D.m_eq_two_mul_varrho_add_two.le)

/-- The linear isomorphism from forms at the definite node (0, m) of grid z onto smooth
algebraic forms of weight (`Data.endWeightData`, `Data.endDetExp`). -/
def endToAlgForm := (D.gridSpace 0 z 0 _).toAlgForm ((D.endWeightData z).2.2.2 0 zero_le)

/-- The two forms, at the nodes (0, m) of both grids, have the levels `Data.endLevel`. -/
abbrev FixedByEndLevels (y : ∀ _, _) := ∀ z,
  D.endToAlgForm z (y z) ∈ levelSpace (algFormRep ..) (endLevel ϑ₁ ..)

/-- The datum of the lift from node (j, m) to (j+1, m): the indicator of the matrix of S on that
edge, on κ₀^(nn′)·vacuum, n, n′ the ranks, κ₀ = `Parameters.vacuumScale`. -/
def endDatum j := P.vacuumScale D.s ^ Fintype.card (D.EndIndex z j.succ × D.EndIndex z j) •
  vacuumDatum (stdSpace ..) (stdSpace ..) _ (Pi.single (S (rowEdge z j D.m)) 1)

abbrev endChain j F := chain (endKernel ϑ z) (endDatum S z) j (D.endToAlgForm z F)

/-- Λ applied to S ↦ the class integral over U(V_{m,m}) of `Data.endPairing` of the two chains of
lifts `Data.endChain`, in grids V and Z, the second read at `Data.endBlockPoint`. -/
def endPeriod (Λ : GridDatum ϑ) (y : ∀ _, _) := Λ fun S ↦ let c z := (endChain S z _ (y z)).1
  classIntegral stdRatPoints (endLevel ϑ ..) fun h ↦ D.endPairing (c _ h) (c _ (endBlockPoint ϑ h))

/-- Crossing a square. Let all (L i, M i) satisfy `SquareLaw` χ ε C, χ⁻¹ the product of the
characters of (p, v), (Q, U), opposite edges having equal characters, with conditions hQ, h
on admissible families, μ-edges, nodes and w. A tidy Λ of order n on w, (p, v), (Q, U) gives
a tidy Φ of order n + 2 on w, (U, R), (v, r), with Λ of M, Fourier transformed in the block
T, equal to C·Φ of L. -/
lemma IsTidy.exists_square_move {P} {D : Data P} {ϑ z a b n w} {Λ : GridDatum ϑ} {p v Q U R} r {T J}
  [Fintype T] (τ : D.GridIndex z a b ≃ D.NodeIndex U) (σ : D.NodeIndex p ⊕ T ≃ D.NodeIndex Q) (ρ :
  D.NodeIndex r ⊕ T ≃ D.NodeIndex R) (ψ : AddChar _ ℂ) {χ ε C} {L M : J → _} (q : ∀ i,
  SquareLaw χ ε C (L i) (M i)) (hQ : ∀ g, @IsAdmissibleFamily _ D ϑ g →
  g R = blockInlGL ρ (g r) ∧ ∀ k, let u := update (update g p k) Q (blockInlGL σ k)
  IsAdmissibleFamily u ∧ u p = k) (h : U ≠ v ∧ (IsMuEdge Q U ∧ ¬IsMuEdge U R ∨ IsMuEdge p v ∧
  ¬IsMuEdge v r) ∧ (∀ q ∈ [U, R, v, r], q.2 ≤ (D.m, D.m) ∧ q ∉ [p, Q]) ∧ ∀ e ∈ w, e.1 ∉ [p, Q] ∧ e.2
  ∉ [p, Q, R, r]) (H : IsTidy n (insert (p, v) (insert (Q, U) w)) Λ) (X : χ = (edgeChar ϑ (p, v) *
  edgeChar ϑ (Q, U))⁻¹ ∧ edgeChar ϑ (U, R) = edgeChar ϑ (p, v) ∧ edgeChar ϑ (v, r) = edgeChar ϑ (Q,
  U) := by simp [edgeChar]) : ∃ Φ, IsTidy (n + 2) (insert (U, R) (insert (v, r) w)) Φ ∧ ∀ f : _ →
  _ → J, DependsOn f w → Λ (fun S ↦ let x := (S (Q, U)).submatrix τ σ; ∑ k, ψ (k * x.toCols₂).trace
    * M (f S k) (fromRows (S (p, v)) x.toCols₁)) = C * Φ fun S ↦ let x := (S (U, R)).submatrix ρ τ
  L (f S x.toRows₂) (fromCols (S (v, r)) x.toRows₁) := by
  obtain ⟨⟨uv, μ, bQ, hw⟩, ⟨_, W, c, s, -, hc, hΛ⟩, d, d₁, d₄⟩ := h, H.2,
    exists_partner_kernel χ ε (Modulus.isValuationPair_resRing _)
  simp [-Prod.forall, LeftInvOnMuEdges] at hw hQ hc bQ
  let y (S : EdgeTuple ϑ) := fromRows (S (p, v)) ((S (Q, U)).submatrix τ σ).toCols₁
  let t S (M : _ × _) : EdgeTuple ϑ := w.piecewise S (update (update 0 (U, R) M.1) (v, r) M.2)
  let G (d : _ → ℂ) := Λ.bind (fun S M ↦ d (y S) * graphKernel χ ε (M.2.fromCols (M.1.submatrix ρ
    τ).toRows₁) (y S) * ψ ((M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace) t
  have I g (hg : IsAdmissibleFamily g) (k : GL (D.NodeIndex p) (gridModulus ϑ).ResRing) d f :
    G (d <| (blockGL (g v, reindexGL τ.symm (g U)))⁻¹.1 * · * k.1) (f <| tupleAction g ·) =
    edgeCharProd g (insert (U, R) (insert (v, r) w)) * G d f := by
    erw [(?_ : edgeCharProd .. = _ / _ * _), mul_assoc, ← H.1 _ ((hQ g hg).2 k).1]
    simp [G, hΛ, mul_sum, graphKernel_equivariant χ ε (blockGL (g v, reindexGL τ.symm (g U))) (g r)
      k _ (y (s _)), W.sum_comm, mul_assoc, mul_left_comm _ (_ / _), -coe_units_inv]
    rw [eq_comm, ← ((injective_gl_inv_mul_mul (g R) (g U)).prodMap
      (injective_gl_inv_mul_mul (g r) (g v))).bijective_of_finite.sum_comp]
    congr! 9 <;> simp [y, t, tupleAction, *, entrywise, ← Matrix.mul_assoc, ← map_inv,
      reindex_equiv σ, reindex_equiv ρ, reindex_equiv τ]
    ext1; simp [piecewise, update]
    split_ifs <;> subst_vars <;> simp [tupleAction, *, ← map_inv]
    simp +contextual [edgeCharProd, mt (hw _), *, MulChar.inv_apply_eq_inv', uv.symm]
    field [MulChar.apply_eq_zero_iff]
  have l S : HasLeftInv (S (Q, U)) → HasLeftInv (y S).toRows₂ := .imp' (·.submatrix (σ ∘ .inl) τ)
    (by simp_all [y, entrywise, reindex_equiv τ])
  refine ⟨G 1, ⟨(I · · 1 1), (LinearMap.ext fun f ↦ ?_ : G 1 = G d) ▸ H.2.bind (by
    simp [sq, mul_le_mul', card_matrix_le_tupleBound, *]) fun S M n m ↦ ?_⟩, fun f hL ↦ ?_⟩
  · simpa +unfoldPartialApp [tupleAction, edgeCharProd, G, hΛ, expect_sum_comm, d₁, ← expect_mul,
      ← mul_expect] using congr(𝔼 k, $(I 1 (by simp [IsAdmissibleFamily]) k d f))
  · simp +contextual [t, uv, mt (hw _), -Prod.forall, LeftInvOnMuEdges] at m ⊢
    obtain ⟨E, e', e⟩ := (d₁ ..).1 (left_ne_zero_of_mul n)
    use E.mul (ψ.toMonoidHom.isOfFinOrder (isMulTorsion_of_finite _)), fun _ ↦ (e' (m.1 (by
      lia))).imp' (·.fromCols 0 |>.submatrix τ.symm ρ.symm) (by simp [entrywise, reindex_equiv ρ,
      reindex_equiv τ]), fun _ ↦ e (l _ (m.2.1 (by lia))), m.2.2
  erw [hΛ, hΛ, mul_sum]; congr with i
  exact (or_not.imp_right (hc i)).elim (by simp [·]) fun ⟨_, m', m, _⟩ ↦ .trans congr(_ * ∑ k, _ *
    $(d₄ _ _ _ (q _) (y _) (μ.symm.imp (m' ·.1) (l _ <| m ·.1)))) (by
    simp [@hL (w.piecewise _ _) _ fun _ ↦ (ite_eq_left ·), t, uv, mt (hw _), sum_prod_type,
      reindex_equiv
      (reindex ρ τ), sum_eq_sum_fromRows, mul_comm (graphKernel ..), sum_eq_sum_fromCols, mul_sum,
      @sum_comm (Matrix T ..), mul_left_comm C, mul_assoc, trace, mul_apply, reindex_equiv τ])
