using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class DephasingTwoClassicalityBlockRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/lonigrochruscinski2022dephasing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-level block measurement has time-dependent two-classical dephasing statistics without mutual unbiasedness.",
        H("Two-classical dephasing without an unbiased measurement"),
        Blocks(
            Paragraph(Text(
                "The system and bath have coordinate types Fin d and Fin m. Matrices have complex entries, "
                    + "and CoeSort.coe displays the carrier of Matrix.unitaryGroup explicitly. Subtype.val gives the "
                    + "underlying matrix of V. The computational rank-one projectors are basisProjector j, "
                    + "and unitaryEvolution U X is UXUᴴ. Matrix.kroneckerMap with scalar multiplication "
                    + "forms the tensor product. Real times are embedded into the complex scalars by Complex.ofReal; "
                    + "the two casts of the natural dimension d are distinguished by their displayed types. "
                    + "Source line numbers refer to dephasing-v2.tex in arXiv:2211.02014v2.")),
            Node("hamiltonian", "hamiltonian", "The dephasing Hamiltonian", HamiltonianFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The Hamiltonian is the sum of the computational system projector tensored with its bath Hamiltonian. "
                    + "This is the Hamiltonian of TeX lines 130–134, specialized to rank-one coordinate projectors "
                    + "and finite-dimensional baths. The definition accepts arbitrary complex bath matrices; "
                    + "Hermiticity is a separate hypothesis of claim."),
            Node("propagator", "propagator", "The joint propagator", PropagatorFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For a time-independent Hamiltonian, the propagator at duration t is exp(−itH). "
                    + "NormedSpace.exp is the matrix exponential. The unitary evolution in TeX lines 70–73 "
                    + "uses this propagator when the Hamiltonian is constant. No sign or positivity restriction "
                    + "on t is part of the definition."),
            Node("measurement-projector", "measurementProjector", "A measurement projector", MeasurementFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The xth column of V determines a rank-one projector. Unitarity makes these columns an "
                    + "orthonormal basis, so the projectors form the sharp measurement of TeX lines 77–79, "
                    + "with the rank-one basis convention of lines 279–289."),
            Node("luders", "luders", "The joint Lüders operation", LudersFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The operation sandwiches X between the outcome projector tensored with the bath identity. "
                    + "It is the unnormalized Lüders operation acting only on the system, as in TeX lines 77–79. "
                    + "The two products are ordinary matrix products."),
            Node("prob1", "prob1", "One-time statistics", Prob1Formula(),
                AssessedProvenance.FromLiterature(Source),
                "Starting from the product ρ ⊗ σ at t₀, evolve to t₁, apply the y outcome operation and "
                    + "take the joint trace. This is equation (2), TeX lines 78–80, for one measurement. "
                    + "The formula is complex-valued and is defined for arbitrary matrices ρ and σ; "
                    + "the density conditions are imposed in claim."),
            Node("prob2", "prob2", "Two-time statistics", Prob2Formula(),
                AssessedProvenance.FromLiterature(Source),
                "Evolve from t₀ to t₁, apply outcome x, evolve for t₂−t₁, apply outcome y, and take the trace. "
                    + "The argument order records the later outcome and time first. This is the two-measurement "
                    + "case of equation (2), TeX lines 78–80, with no reset of the bath between measurements."),
            Node("two-classical", "twoClassical", "Consistency through two measurements", TwoClassicalFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For every t₀ ≤ t₁ ≤ t₂, the one-time law is normalized and both marginals of the two-time "
                    + "law equal the corresponding one-time law. Thus omitting either measurement agrees with "
                    + "summing over its outcome. These are precisely the consistency requirements through "
                    + "two measurements in TeX lines 82–90; no assertion about three measurements is included."),
            Node("time-dependent", "timeDependent", "Actual dependence on the measurement times", TimeDependentFormula(),
                AssessedProvenance.FromRepo(Source),
                "For fixed initial data and fixed outcomes x and y, two ordered time pairs give different "
                    + "two-time values. Both pairs start at or after t₀. This explicit nonconstancy condition "
                    + "supplements the incompatibility discussed at TeX line 201."),
            Node("not-fully-compatible", "notFullyCompatible", "Noncommuting measurement and dephasing projectors",
                CompatibilityFormula(), AssessedProvenance.FromLiterature(Source),
                "Some measurement projector fails to commute with some computational projector. "
                    + "This is the failure of full compatibility in TeX line 201. The definition involves "
                    + "the two sharp measurements, independently of the bath state or the time parameters."),
            Node("claim", "claim", "The proposed necessity of mutual unbiasedness", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every finite system and bath, take Hermitian bath Hamiltonians and positive semidefinite "
                    + "unit-trace bath and system matrices. Assume the system matrix is diagonal in the dephasing "
                    + "basis and differs from the maximally mixed matrix. If the measurement is not fully compatible, "
                    + "its statistics are two-classical and its two-time law is nonconstant, claim requires every "
                    + "squared measurement entry to be 1/d. This is a finite-dimensional necessity statement "
                    + "suggested by the conjecture at TeX line 347. The source's phase-modified Fourier family "
                    + "at lines 284–289 is unbiased; the displayed conclusion asks only for unbiasedness. "
                    + "The additional nonconstancy hypothesis makes the meaning of time dependence explicit. "
                    + "No positive lower bound on d or m is added to the quantified statement."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A block measurement contradicts the necessity statement"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 3, m = 2 and t₀ = 0. Put Z = diag(1,−1), H₀ = 0, H₁ = Z, H₂ = 2Z, "
                            + "σ = I₂/2 and ρ = diag(1/2,1/3,1/6). Choose the measurement columns "
                            + "(e₀+e₁)/√2, (e₀−e₁)/√2 and e₂, in that order. The amplitude 1/√2 is real "
                            + "and has square 1/2, which proves that the three-column matrix is unitary. "
                            + "Its projectors are the matrices with upper 2 by 2 blocks "
                            + "½[[1,1],[1,1]] and ½[[1,−1],[−1,1]], and the projector onto e₂.")),
                    Paragraph(Text(
                        "The bath matrix is positive definite and has trace one. The three positive diagonal "
                            + "entries of ρ prove positivity and sum to one. Its off-diagonal entries vanish, "
                            + "and its (0,0) entry is 1/2 rather than 1/3, so it is not maximally mixed. "
                            + "The three bath Hamiltonians are Hermitian.")),
                    Paragraph(Text(
                        "On the joint coordinate (j,b), the Hamiltonian is diagonal with energy j for b = 0 "
                            + "and −j for b = 1. Applying the matrix exponential to this diagonal matrix gives "
                            + "the diagonal propagator with entries exp(−itE). Conjugating a matrix X therefore "
                            + "multiplies its (k,l) entry by exp(−it(Eₖ−Eₗ)). Both the initial product and the "
                            + "Hamiltonian are diagonal, so the initial product is stationary.")),
                    Paragraph(Text(
                        "Sandwiching the initial product by an outcome projector gives pₓPₓ ⊗ σ, where "
                            + "(p₀,p₁,p₂) = (5/12,5/12,1/6). Taking its trace proves that the one-time law "
                            + "equals this same vector at every time. For the second measurement, idempotence "
                            + "of Pᵧ and cyclicity of the trace reduce the Lüders trace to "
                            + "Tr((Pᵧ ⊗ I₂)X). Inserting the entrywise evolution into this trace evaluates "
                            + "the two-time law at u = t₂−t₁ as the matrix [[a,b,0],[b,a,0],[0,0,1/6]], "
                            + "where a = 5(2+exp(iu)+exp(−iu))/48 and b = 5(2−exp(iu)−exp(−iu))/48. "
                            + "The row is y and the column is x.")),
                    Paragraph(Text(
                        "Since a+b = 5/12, every row sum and every column sum equals the corresponding "
                            + "one-time value; those values sum to one. This proves all three two-classical "
                            + "consistency conditions. For x = y = 0, the ordered pairs (t₁,t₂) = (0,0) "
                            + "and (0,π) give respectively 5/12 and 0, using exp(iπ) = exp(−iπ) = −1. "
                            + "Thus the two-time law is nonconstant.")),
                    Paragraph(Text(
                        "For the first measurement projector and the computational projector at 0, "
                            + "the (0,1) entries of their products in the two orders are 0 and 1/2. "
                            + "They do not commute. Finally the (2,0) measurement entry is zero, whose "
                            + "squared norm is 0 rather than 1/3. Applying claim to these matrices would "
                            + "force that squared norm to equal 1/3, a contradiction. The failure concerns "
                            + "necessity of unbiasedness; the sufficiency statement for unbiased bases "
                            + "in TeX lines 326–346 is not contradicted."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lonigro-chruscinski-2022-dephasing-two-classicality-refutation"),
                    ResolutionKind.Refuted)),
            NativeApplication())));

    private static DocumentBlock NativeApplication() => new DocumentBlock.Section(
        H("A stationary five-mode application with no common reducing projection"), Blocks(
        Paragraph(Text(
            "Use the mode order (0,1,2,3,13) = (000,100,010,001,101), with coordinate projectors Pₓ. "
                + "The original waiting/read model has the following real symmetric Hamiltonian K, "
                + "waits U(t) = exp(−itK) for t ≥ 0, all density matrices as inputs, complete rank-one "
                + "Lüders reads, finite classical outcome feedback and Stop. No phase gate, coarse-block "
                + "instrument, energy measurement or additional preparation is added to this menu.")),
        new DocumentBlock.DisplayFormula(Disp(Equal(X("K"), Seq(Begin, Grp(X("pmatrix")),
            D(0), Amp, D(1), Amp, D(1), Amp, D(1), Amp, D(0), RowBreak,
            D(1), Amp, D(0), Amp, D(0), Amp, D(0), Amp, D(1), RowBreak,
            D(1), Amp, D(0), Amp, D(0), Amp, D(0), Amp, D(0), RowBreak,
            D(1), Amp, D(0), Amp, D(0), Amp, D(0), Amp, D(1), RowBreak,
            D(0), Amp, D(1), Amp, D(0), Amp, D(1), Amp, D(0), End, Grp(X("pmatrix")))))),
        new DocumentBlock.DisplayFormula(Disp(Equal(At(X("ρ"), X("ε")), new Formula.Binary(
            Divide(X("I"), D(5)), FormulaBinaryOperator.Add, Smul(X("ε"), X("K")))))),
        Paragraph(Text(
            "For every real ε > 0 with 5ε‖K‖op < 1, where the norm is the Euclidean operator norm, "
                + "ρ(ε) is positive semidefinite, has trace one and differs from I₅/5. Indeed, the "
                + "self-adjoint bound K ≥ −‖K‖op I gives ρ(ε) ≥ (1/5−ε‖K‖op)I ≥ 0; the diagonal "
                + "of K vanishes and its (0,1) entry is one. Every wait fixes ρ(ε), because it is an "
                + "affine polynomial in K. A spectral unitary W gives WᴴKW = diag(λⱼ) and "
                + "Wᴴρ(ε)W = diag(1/5+ελⱼ). The eigenvalues λⱼ are distinct: an eigenvector of K "
                + "whose mode-1 coordinate vanishes must be zero, as follows from its five row equations; "
                + "two independent eigenvectors of the same eigenvalue would yield such a vector. "
                + "Consequently these density eigenvalues are nonuniform for every allowed ε.")),
        Paragraph(Text(
            "Take the dephasing coordinates to be this passive energy frame, d = 5, m = 1, "
                + "σ = [1], Hⱼ = [λⱼ], the system input Wᴴρ(ε)W, and measurement matrix V = Wᴴ. "
                + "The measurement projectors are WᴴPₓW. The map X ↦ (WᴴXW) ⊗ [1], with the "
                + "canonical identification of the one-dimensional bath coordinate, preserves products, "
                + "adjoints, scalar multiplication, exponentials and trace. It maps K to the literal "
                + "hamiltonian Hs, U(t) to propagator Hs t, and each native branch to luders V x. "
                + "Thus it transports the intervened joint trace formula itself, without a reduced-channel "
                + "regression or a bath reset. The change of coordinates supplies no physical operation.")),
        new DocumentBlock.DisplayFormula(Disp(new Formula.Aligned([
            Equal(At(X("P₁"), X("x"), X("t₁")), Divide(D(1), D(5))),
            Equal(At(X("P₂"), X("y"), X("t₂"), X("x"), X("t₁")),
                Divide(new Formula.Power(Seq(Left, Lvert, Sp,
                    new Formula.Subscript(At(X("U"), Subtract(X("t₂"), X("t₁"))), Seq(X("y"), X("x"))),
                    Right, Rvert), D(2)), D(5)))
        ]))),
        Paragraph(Text(
            "These are prob1 and prob2 for every t₀ ≤ t₁ ≤ t₂ and every pair of outcomes, with the "
                + "same fixed initial data. Stationarity gives Pₓρ(ε)Pₓ = Pₓ/5, so the first outcome "
                + "has weight 1/5 and its conditional state is Pₓ. Unitarity makes every row and column "
                + "sum of |U(u)ᵧₓ|² equal to one. The one-time law is therefore normalized and both "
                + "two-time marginals are 1/5 for every ordered pair, proving twoClassical. The law is "
                + "nonconstant: the (0,1) transition probability is zero at duration zero and positive "
                + "at sufficiently small positive durations, since its real-frame amplitude has "
                + "derivative one at zero. This supplies timeDependent as defined above.")),
        Paragraph(Text(
            "The two PVMs have no nontrivial common orthogonal reducing projection. In native "
                + "coordinates, a matrix Q commuting with all Pₓ is diagonal. Commuting also with K "
                + "forces equality along the edges 0–1, 0–2, 0–3 and 1–13, so Q is scalar. In the energy frame, "
                + "commuting with all energy projectors implies commuting with diag(λⱼ); conjugating "
                + "back gives precisely the preceding pair of commutation conditions. An idempotent "
                + "scalar is zero or one. The simple spectrum makes these rank-one energy projectors "
                + "the distinct spectral projectors. Nevertheless the measurement is not mutually "
                + "unbiased: (0,1,0,−1,0) is a nonzero zero-energy vector, and every zero-energy "
                + "eigenvector has mode-0 coordinate zero by row 2 of K. Hence an entry Vⱼ₀ is zero, "
                + "rather than having squared norm 1/5. Full compatibility is also excluded, since "
                + "a mode projector would otherwise be a nontrivial common reducing projection.")),
        Paragraph(Text(
            "Let D = diag(1,i,i,i,1). Then DᴴKD = iA, where A is "
                + "FiveModeRealWaitSpan.generator, and DᴴU(t)D is the entrywise complex embedding "
                + "of the real orthogonal matrix exp(tA). The transformed state is I₅/5+iεA; its "
                + "entrywise real part equals that of I₅/5. The Hermitian-input theorem "
                + "FiveModeRealResponse.five_mode_real_response_fiber therefore gives equality of "
                + "every finite complete-record law. Conjugation fixes each mode projector, intertwines "
                + "the waits and preserves trace; induction on RankOneFeedbackProtocol.Protocol "
                + "transports the equality back, including every feedback branch and Stop. "
                + "Thus the nonuniform density spectrum is invisible to this entire permitted "
                + "predictive interface, rather than only to one-time populations.")),
        Paragraph(Text(
            "This preparation aliasing does not make insertion of a measurement noninvasive. "
                + "Use the native return experiment of SelfGeneratedPredictiveMemory §16: first outcome "
                + "N = 000 at time 0, last outcome N at 2t, with a full intermediate mode read at t "
                + "in the inserted experiment. Its first branch is exactly P_N/5. Writing p_A for "
                + "the return probability from P_N without the intermediate read and p_B for the "
                + "sum over its intermediate outcomes, the two joint probabilities are p_A/5 and "
                + "p_B/5. In the real frame p_A = exp(2tA)₀₀² and "
                + "p_B = ∑ⱼ exp(tA)₀ⱼ² exp(tA)ⱼ₀². Their difference g has g(0) = g′(0) = 0 and "
                + "g″(0) = 4∑ⱼ A₀ⱼ² > 0. The derivative sign theorem followed by the mean-value "
                + "theorem gives one δ > 0 for which p_B > p_A whenever 0 < t < δ. "
                + "The joint insertion gap is therefore (p_B−p_A)/5 > 0, uniformly in the allowed ε. "
                + "The same scalar-bath trace transport proves this three-time consistency violation "
                + "in the dephasing frame. It reuses the native insertion mechanism; it asserts "
                + "neither consistency at every order nor an inequality at every positive time.")),
        Paragraph(Text(
            "This existing-result synthesis rules out the proposed repair that merely excludes "
                + "nontrivial common reducing projections of the energy and mode PVMs. The block "
                + "refutation above remains its own three-level result. The five-mode application "
                + "supplies complex Hilbert-space density matrices, Born probabilities, Lüders branches "
                + "and the fixed coherent Hamiltonian as model principles. It derives no such operations "
                + "from ignorance, information conservation or the five-mode support alone. The scalar "
                + "bath describes closed coherent dynamics and gives no retained-environment extension. "
                + "Acquiring the required preparations, phase references and composition law from the "
                + "native predictive contract remains a separate quantum-origin problem. No physical "
                + "realization or literature-novelty claim is made."))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula HamiltonianFormula() => Dimensions(All("Hs", Hamiltonians(),
        Equal(Typed(LocalCall("hamiltonian", X("Hs")), JointMatrix()),
            SumOver("j", FinOf(X("d")), Tensor(Basis(X("j")), At(X("Hs"), X("j")))))));

    private static Formula PropagatorFormula() => Dimensions(All("Hs", Hamiltonians(), All("t", Reals(),
        Equal(Typed(LocalCall("propagator", X("Hs"), X("t")), JointMatrix()),
            At(Qualified("NormedSpace", "exp"), Smul(
                Multiply(new Formula.Negate(At(Qualified("Complex", "ofReal"), X("t"))),
                    Qualified("Complex", "I")), LocalCall("hamiltonian", X("Hs"))))))));

    private static Formula MeasurementFormula() => All("d", Naturals(), All("V", MeasurementType(),
        All("x", FinOf(X("d")), Equal(Typed(LocalCall("measurementProjector", X("V"), X("x")), SystemMatrix()),
            At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"),
                LambdaOf("i", FinOf(X("d")), At(UnderlyingV(), X("i"), X("x"))))))));

    private static Formula LudersFormula() => Dimensions(All("V", MeasurementType(), All("x", FinOf(X("d")),
        All("X", JointMatrix(), Equal(Typed(LocalCall("luders", X("V"), X("x"), X("X")), JointMatrix()),
            Multiply(Multiply(Tensor(LocalCall("measurementProjector", X("V"), X("x")),
                Typed(D(1), BathMatrix())), X("X")),
                Tensor(LocalCall("measurementProjector", X("V"), X("x")), Typed(D(1), BathMatrix()))))))));

    private static Formula Prob1Formula() => Parameters(All("y", FinOf(X("d")), All("t₁", Reals(),
        Equal(Typed(P1(X("y"), X("t₁")), Complexes()),
            Trace(LocalCall("luders", X("V"), X("y"), InitialEvolution(X("t₁"))))))));

    private static Formula Prob2Formula()
    {
        Formula first = LocalCall("luders", X("V"), X("x"), InitialEvolution(X("t₁")));
        Formula evolved = Evolution(LocalCall("propagator", X("Hs"), Subtract(X("t₂"), X("t₁"))), first);
        Formula value = Trace(LocalCall("luders", X("V"), X("y"), evolved));
        return Parameters(All("y", FinOf(X("d")), All("t₂", Reals(), All("x", FinOf(X("d")), All("t₁", Reals(),
            Equal(Typed(P2(X("y"), X("t₂"), X("x"), X("t₁")), Complexes()), value))))));
    }

    private static Formula TwoClassicalFormula()
    {
        Formula normalized = Equal(SumOver("x", FinOf(X("d")), P1(X("x"), X("t₁"))), Typed(D(1), Complexes()));
        Formula later = All("y", FinOf(X("d")), Equal(
            SumOver("x", FinOf(X("d")), P2(X("y"), X("t₂"), X("x"), X("t₁"))), P1(X("y"), X("t₂"))));
        Formula earlier = All("x", FinOf(X("d")), Equal(
            SumOver("y", FinOf(X("d")), P2(X("y"), X("t₂"), X("x"), X("t₁"))), P1(X("x"), X("t₁"))));
        return Parameters(Equivalence(DataCall("twoClassical"), All("t₁", Reals(), All("t₂", Reals(),
            Arrow(LE(X("t₀"), X("t₁")), Arrow(LE(X("t₁"), X("t₂")),
                Conjunction(normalized, Conjunction(later, earlier))))))));
    }

    private static Formula TimeDependentFormula()
    {
        Formula different = Some("x", FinOf(X("d")), Some("y", FinOf(X("d")), NotEqual(
            P2(X("y"), X("t₂"), X("x"), X("t₁")), P2(X("y"), X("t₂'"), X("x"), X("t₁'")))));
        Formula ordered = Conjunction(LE(X("t₀"), X("t₁")), Conjunction(LE(X("t₁"), X("t₂")),
            Conjunction(LE(X("t₀"), X("t₁'")), Conjunction(LE(X("t₁'"), X("t₂'")), different))));
        return Parameters(Equivalence(DataCall("timeDependent"), Some("t₁", Reals(), Some("t₂", Reals(),
            Some("t₁'", Reals(), Some("t₂'", Reals(), ordered))))));
    }

    private static Formula CompatibilityFormula() => All("d", Naturals(), All("V", MeasurementType(),
        Equivalence(LocalCall("notFullyCompatible", X("V")), Some("x", FinOf(X("d")), Some("j", FinOf(X("d")),
            NotEqual(Multiply(LocalCall("measurementProjector", X("V"), X("x")), Basis(X("j"))),
                Multiply(Basis(X("j")), LocalCall("measurementProjector", X("V"), X("x")))))))));

    private static Formula ClaimFormula()
    {
        Formula conclusion = All("j", FinOf(X("d")), All("x", FinOf(X("d")), Equal(
            At(Qualified("Complex", "normSq"), At(UnderlyingV(), X("j"), X("x"))),
            Divide(Typed(D(1), Reals()), NatCast(X("d"), Reals())))));
        Formula diagonal = All("i", FinOf(X("d")), All("j", FinOf(X("d")), Arrow(NotEqual(X("i"), X("j")),
            Equal(At(X("ρ"), X("i"), X("j")), Typed(D(0), Complexes())))));
        Formula hermitian = All("j", FinOf(X("d")), At(Qualified("Matrix", "IsHermitian"), At(X("Hs"), X("j"))));
        Formula nonmixed = NotEqual(X("ρ"), Smul(Divide(Typed(D(1), Complexes()), NatCast(X("d"), Complexes())),
            Typed(D(1), SystemMatrix())));
        return Equivalence(Local("claim"), Parameters(Arrow(hermitian,
            Arrow(At(Qualified("Matrix", "PosSemidef"), X("σ")),
                Arrow(Equal(Trace(X("σ")), Typed(D(1), Complexes())),
                    Arrow(At(Qualified("Matrix", "PosSemidef"), X("ρ")),
                        Arrow(Equal(Trace(X("ρ")), Typed(D(1), Complexes())), Arrow(diagonal, Arrow(nonmixed,
                            Arrow(LocalCall("notFullyCompatible", X("V")),
                                Arrow(DataCall("twoClassical"), Arrow(DataCall("timeDependent"), conclusion))))))))))));
    }

    private static Formula Parameters(Formula body) => Dimensions(All("Hs", Hamiltonians(),
        All("σ", BathMatrix(), All("ρ", SystemMatrix(), All("V", MeasurementType(), All("t₀", Reals(), body))))));
    private static Formula Dimensions(Formula body) => All("d", Naturals(), All("m", Naturals(), body));
    private static Formula DataCall(string name) => LocalCall(name, X("Hs"), X("σ"), X("ρ"), X("V"), X("t₀"));
    private static Formula P1(Formula y, Formula time1) => LocalCall("prob1", X("Hs"), X("σ"), X("ρ"), X("V"), X("t₀"), y, time1);
    private static Formula P2(Formula y, Formula time2, Formula x, Formula time1) =>
        LocalCall("prob2", X("Hs"), X("σ"), X("ρ"), X("V"), X("t₀"), y, time2, x, time1);
    private static Formula InitialEvolution(Formula time1) => Evolution(
        LocalCall("propagator", X("Hs"), Subtract(time1, X("t₀"))), Tensor(X("ρ"), X("σ")));
    private static Formula Evolution(Formula u, Formula x) =>
        At(Qualified("D5", "S3", "Quantum", "Decoherence", "ProjectedUnistochasticDynamics", "unitaryEvolution"), u, x);
    private static Formula Basis(Formula j) =>
        At(Qualified("D5", "S3", "Quantum", "Decoherence", "ProjectedUnistochasticDynamics", "basisProjector"), j);
    private static Formula UnderlyingV() => At(Qualified("Subtype", "val"), X("V"));
    private static Formula Trace(Formula x) => At(Qualified("Matrix", "trace"), x);
    private static Formula Tensor(Formula a, Formula b) => At(Qualified("Matrix", "kroneckerMap"),
        LambdaOf("x1", Complexes(), LambdaOf("x2", Complexes(), Multiply(X("x1"), X("x2")))), a, b);
    private static Formula Hamiltonians() => Arrow(FinOf(X("d")), BathMatrix());
    private static Formula MeasurementType() => At(Qualified("CoeSort", "coe"),
        At(Qualified("Matrix", "unitaryGroup"), FinOf(X("d")), Complexes()));
    private static Formula SystemMatrix() => MatrixType(FinOf(X("d")));
    private static Formula BathMatrix() => MatrixType(FinOf(X("m")));
    private static Formula JointMatrix() => MatrixType(Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("m")))));
    private static Formula MatrixType(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula NatCast(Formula n, Formula type) => Typed(At(Qualified("Nat", "cast"), n), type);
    private static Formula X(string name) => name switch
    {
        "σ" => SigmaLower,
        "ε" => Varepsilon,
        "P₁" => new Formula.Subscript(F.Id("P"), D(1)),
        "P₂" => new Formula.Subscript(F.Id("P"), D(2)),
        "ρ" => Rho,
        "t₀" => new Formula.Subscript(F.Id("t"), D(0)),
        "t₁" => new Formula.Subscript(F.Id("t"), D(1)),
        "t₂" => new Formula.Subscript(F.Id("t"), D(2)),
        "t₁'" => Seq(new Formula.Subscript(F.Id("t"), D(1)), Apos),
        "t₂'" => Seq(new Formula.Subscript(F.Id("t"), D(2)), Apos),
        _ => F.Id(name)
    };
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Decoherence",
        "DephasingTwoClassicalityBlockRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Conjunction(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
}
