using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class UltrafineThreeProductObservablesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/UltrafineThreeProductObservables";
    private const string DensityModule = "D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation";
    private const string PureModule = "D5/S3/Quantum/PureState/PureStateHandshake";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/gachechiladzewyderkaguhne2018ultrafine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three Hermitian product observables have useless pairs and a useful triple on two qutrits.",
        H("Pairwise and joint entanglement detection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ultrafine-three-product-is-separable"),
                DeclarationHandle.Create(Module + ".IsSeparable"),
                H("Separable matrices"),
                StatementSource.FromAuthor(Disp(SeparableDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For natural dimensions m and n, a complex matrix on Fin m × Fin n is separable "
                        + "when it belongs to the real convex hull of projectors onto normalized product vectors. "
                        + "The source defines separable states as the convex hull of pure product states "
                        + "in uew-iop-revision.tex, lines 113–114. Convex hull here means finite convex combinations.")),
                    Paragraph(Text("The projector is "), Ref(PureModule + ".rankOneDensity"), Text(
                        ": its entries are the vector coordinates times the conjugate coordinates. "
                        + "The two normalization equations use complex-valued dot products and the complex scalar one. "
                        + "The definition permits unequal dimensions, including zero dimensions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ultrafine-three-product-is-useless"),
                DeclarationHandle.Create(Module + ".IsUseless"),
                H("Expectation values reproducible by separable states"),
                StatementSource.FromAuthor(Disp(UselessDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "A finite selection s from an arbitrarily indexed family obs is useless when every density "
                        + "matrix has a separable density matrix with the same complex trace expectation for every "
                        + "selected observable. Both parties have dimension d. The same matrix σ must reproduce "
                        + "all the selected expectations simultaneously. The source describes uselessness in "
                        + "uew-iop-revision.tex, lines 504–507.")),
                    Paragraph(Text("Density means positive semidefinite with trace equal to one, using "),
                        Ref(DensityModule + ".IsDensity"), Text(
                        ". This predicate places no Hermitian or product condition on obs; those conditions "
                        + "are supplied separately in the existence statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ultrafine-three-product-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Three product observables with no useful pair"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "There exist two families a and b of three Hermitian three-by-three complex matrices. "
                    + "Every pair of distinct indices gives a useless pair of their Kronecker products, whereas "
                    + "the whole triple is useful. The indices are the elements of Fin 3, namely zero, one and two. "
                    + "This answers the source's request to identify such a triple "
                    + "in uew-iop-revision.tex, lines 748–752, by fixing both local dimensions to three. "
                    + "Usefulness means that some density matrix has no separable density matrix matching "
                    + "all three expectations; it asserts neither a classification nor a noise bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ultrafine-three-product-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("An explicit two-qutrit triple"),
                StatementSource.FromAuthor(Disp(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Set δ = 1/100. On the first party take A₀ = diag(1,1,δ), "
                        + "A₁ = X ⊕ [δ] and A₂ = Z ⊕ [δ], where X has rows (0,1), (1,0), "
                        + "and Z = diag(1,−1). On the second party take B₀ with rows "
                        + "(2,1,0), (1,2,1), (0,1,2), B₁ = diag(1,2,3), and B₂ = diag(1,4,9). "
                        + "All entries are complex scalars. Define Mᵢ = Aᵢ ⊗ Bᵢ and H = M₀ + M₁ + M₂. "
                        + "The six local matrices are real symmetric, hence Hermitian.")),
                    Paragraph(Text(
                        "First consider a matrix of the form Σₖ |uₖ⟩⟨uₖ| ⊗ cₖ, where the uₖ are columns "
                        + "of a unitary matrix, each cₖ is positive semidefinite, and the total trace is one. "
                        + "Spectrally decompose each cₖ. Its nonnegative eigenvalues are weights for normalized "
                        + "product projectors, and the trace condition makes their total weight one. "
                        + "The Kronecker product of two rank-one projectors is the projector onto the product "
                        + "vector, so this matrix belongs to the defining convex hull.")),
                    Paragraph(Text(
                        "Suppose a unitary matrix simultaneously diagonalizes the selected first-party factors. "
                        + "Let qₖ = |uₖ⟩⟨uₖ| and pₖ = qₖ ⊗ I. For a density matrix ρ, put "
                        + "cₖ = Vₖ*ρVₖ, where Vₖ sends b to uₖ ⊗ b, and set σ = Σₖ qₖ ⊗ cₖ. "
                        + "Each cₖ is positive semidefinite and σ = Σₖ pₖρpₖ. The pₖ are Hermitian "
                        + "orthogonal projections summing to I, so this unread projective measurement "
                        + "preserves trace and positivity. The block decomposition just proved makes σ separable. "
                        + "Each pₖ commutes with every selected product observable. Cyclicity of trace, "
                        + "pₖ² = pₖ and Σₖ pₖ = I therefore show that σ preserves all their expectations.")),
                    Paragraph(Text(
                        "If the selected second-party factors are simultaneously diagonal instead, interchange "
                        + "the tensor coordinates, apply the same construction, and interchange them back. "
                        + "This real linear reindexing preserves products, trace and positivity; it also sends "
                        + "each normalized product projector to a normalized product projector and therefore "
                        + "preserves their convex hull.")),
                    Paragraph(Text(
                        "For indices zero and one, use the unitary which is the Hadamard matrix on the first "
                        + "two coordinates and fixes the third: its nontrivial entries are ±1/√2. "
                        + "It simultaneously diagonalizes A₀ and A₁. For zero and two, A₀ and A₂ are already "
                        + "diagonal. For one and two, B₁ and B₂ are already diagonal. These three cases and "
                        + "symmetry of the two-element selection prove uselessness for every distinct pair. "
                        + "The source's commuting-factor observation is in uew-iop-revision.tex, lines 679–683; "
                        + "the matrices and the dephasing construction here specify the example explicitly.")),
                    Paragraph(Text(
                        "Next H is Hermitian, so choose a normalized eigenvector g for its least real eigenvalue μ. "
                        + "The spectral lower bound gives H − (μ : ℂ)I positive semidefinite. "
                        + "Its diagonal entry at the tensor coordinate (1,2) is −7 − μ, hence μ ≤ −7 < 0. "
                        + "For the third first-party coordinate, the relevant second-party sum is "
                        + "B₀ + B₁ + B₂ = diag(3,6,13) + vv* + ww*, with v = (1,1,0) and w = (0,1,1). "
                        + "This sum is positive semidefinite.")),
                    Paragraph(Text(
                        "Assume that a normalized product vector a ⊗ b were an eigenvector for this negative μ. "
                        + "The equation in its third first-party coordinate is "
                        + "a₂(B₀ + B₁ + B₂)b = 100(μ : ℂ)a₂b. If a₂ were nonzero, cancellation and "
                        + "the normalization of b would contradict the positive semidefinite quadratic form "
                        + "of B₀ + B₁ + B₂. Thus a₂ = 0, and normalization ensures a₀ ≠ 0 or a₁ ≠ 0.")),
                    Paragraph(Text(
                        "Eliminate the common terms from the two remaining first-party equations. "
                        + "With c = a₁² − a₀², e = 2a₀a₁ and w = (1,2,3), the resulting equations are "
                        + "(c wᵢ + e wᵢ²)bᵢ = 0 for every second-party coordinate i. "
                        + "If bᵢ and bⱼ are nonzero at distinct coordinates, the determinant "
                        + "wᵢwⱼ² − wⱼwᵢ² is nonzero: for increasing indices its values are 2, 6 and 6. "
                        + "The two equations force c = e = 0, hence a₀ = a₁ = 0, a contradiction. "
                        + "Consequently b has exactly one nonzero coordinate k. If k is zero or two, "
                        + "the equations at coordinate one force a₀ = a₁ = 0; if k is one, use coordinate zero. "
                        + "These equations use the adjacent off-diagonal entries of B₀. "
                        + "This excludes every normalized product eigenvector at μ.")),
                    Paragraph(Text(
                        "For a normalized product vector v, the positive semidefinite matrix "
                        + "Q = H − (μ : ℂ)I now satisfies Qv ≠ 0. The zero-quadratic-form criterion for "
                        + "positive semidefinite matrices gives Re(v*Qv) > 0. "
                        + "The rank-one expectation identity from "), Ref(PureModule + ".pure_state_handshake"), Text(
                        " then gives Re Tr(|v⟩⟨v|H) > μ. The real functional σ ↦ Re Tr(σH) is linear, "
                        + "and the strict half-space above μ is convex. It contains every normalized product "
                        + "projector, so it contains their convex hull: every separable σ has energy strictly above μ.")),
                    Paragraph(Text(
                        "Finally ρ = |g⟩⟨g| is a density matrix and Tr(ρH) = (μ : ℂ). "
                        + "If a separable density matrix σ matched all three expectations of ρ, adding those "
                        + "three equalities would give Tr(σH) = (μ : ℂ), contradicting the strict separable "
                        + "energy bound. The displayed families therefore have useless pairs and a useful triple."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gachechiladze-wyderka-guhne-2018-three-product-observables"),
                    ResolutionKind.Proved)))));

    private static Formula SeparableDefinition()
    {
        Formula matrix = BipartiteMatrix(X("m"), X("n"));
        Formula vector = LambdaOf("p", Product(FinOf(X("m")), FinOf(X("n"))),
            Multiply(At(X("a"), At(Qualified("Prod", "fst"), X("p"))),
                At(X("b"), At(Qualified("Prod", "snd"), X("p")))));
        Formula projectors = Seq(OpenBrace, Typed(Tau, matrix), Sp, Mid, Sp,
            Some("a", Arrow(FinOf(X("m")), Complexes()),
                Some("b", Arrow(FinOf(X("n")), Complexes()),
                    Conjunction(UnitVector(X("a")), Conjunction(UnitVector(X("b")),
                        Equal(Tau, RankOne(vector)))))), CloseBrace);
        return All("m", Naturals(), All("n", Naturals(), All("σ", matrix,
            Equivalence(LocalCall("IsSeparable", SigmaLower),
                Member(SigmaLower, At(Qualified("convexHull"), Reals(), projectors))))));
    }

    private static Formula UselessDefinition()
    {
        Formula matrix = BipartiteMatrix(X("d"), X("d"));
        Formula match = All("i", Iota, Arrow(Member(X("i"), X("s")),
            Equal(Trace(Multiply(SigmaLower, At(X("obs"), X("i")))),
                Trace(Multiply(Rho, At(X("obs"), X("i")))))));
        Formula body = All("ρ", matrix, Arrow(Density(Rho), Some("σ", matrix,
            Conjunction(Density(SigmaLower), Conjunction(LocalCall("IsSeparable", SigmaLower), match)))));
        return All("d", Naturals(), All("ι", Seq(Qualified("Type"), Star),
            All("obs", Arrow(Iota, matrix), All("s", At(Qualified("Finset"), Iota),
                Equivalence(LocalCall("IsUseless", X("obs"), X("s")), body)))));
    }

    private static Formula ClaimProposition()
    {
        Formula family = Arrow(FinOf(D(3)), MatrixType(FinOf(D(3)), FinOf(D(3))));
        Formula observables = LambdaOf("k", FinOf(D(3)),
            At(Qualified("Matrix", "kronecker"), At(X("a"), X("k")), At(X("b"), X("k"))));
        Formula hermitian = All("i", FinOf(D(3)),
            Conjunction(At(Qualified("Matrix", "IsHermitian"), At(X("a"), X("i"))),
                At(Qualified("Matrix", "IsHermitian"), At(X("b"), X("i")))));
        Formula pair = Typed(Seq(OpenBrace, X("i"), Comma, Sp, X("j"), CloseBrace),
            At(Qualified("Finset"), FinOf(D(3))));
        Formula pairs = All("i", FinOf(D(3)), All("j", FinOf(D(3)),
            Arrow(NotEqual(X("i"), X("j")), LocalCall("IsUseless", observables, pair))));
        Formula triple = new Formula.Not(Parenthesized(LocalCall("IsUseless", observables,
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinOf(D(3)))))));
        return Some("a", family, Some("b", family, Conjunction(hermitian, Conjunction(pairs, triple))));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements",
        "UltrafineThreeProductObservables", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Density(Formula value) => At(Qualified("D5", "S3", "Quantum", "Entanglement",
        "StructuredNegativityCoincidenceRefutation", "IsDensity"), value);
    private static Formula RankOne(Formula value) => At(Qualified("D5", "S3", "Quantum", "PureState",
        "PureStateHandshake", "rankOneDensity"), value);
    private static Formula UnitVector(Formula value) => Equal(
        At(Qualified("dotProduct"), At(Qualified("star"), value), value), Typed(D(1), Complexes()));
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula MatrixType(Formula rows, Formula columns) =>
        At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula BipartiteMatrix(Formula m, Formula n) =>
        MatrixType(Product(FinOf(m), FinOf(n)), Product(FinOf(m), FinOf(n)));
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name switch
    {
        "σ" => SigmaLower,
        "τ" => Tau,
        "ρ" => Rho,
        "ι" => Iota,
        _ => F.Id(name),
    };
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
}
