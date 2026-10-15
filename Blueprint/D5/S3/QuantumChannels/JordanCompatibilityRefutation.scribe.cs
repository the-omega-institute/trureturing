using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class JordanCompatibilityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/JordanCompatibilityRefutation.";
    private const string MatrixMaps =
        "D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap";
    private const string Channel =
        "D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction.IsChannel";
    private const string PartialTraces =
        "D5.S3.Quantum.Information.PartialTraceMutualInformation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/girardplavalasikora2021jordan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two compatible channels on four-dimensional complex matrices need not be Jordan compatible.",
        H("Compatibility need not imply Jordan compatibility"), Blocks(
            Node("Mat", "Complex square matrices", MatFormula(),
                "For an index type of any universe, Mat is the type of complex square matrices on that type.",
                AssessedProvenance.FromRepo()),
            Node("Map", "Complex linear maps between matrix spaces", MapFormula(),
                "Map is the MatrixMap abbreviation for complex linear maps between the two square-matrix spaces. Both index types may belong to arbitrary universes.",
                AssessedProvenance.FromRepo()),
            new DocumentBlock.Section(H("Matrix conventions"), Blocks(
                Paragraph(Text(
                    "The tensor index is Fin d × (Fin d × Fin d), with the reference coordinate first. "
                        + "Fin d includes every natural d, including zero. Products below retain this association. "
                        + "A centered dot denotes matrix multiplication for matrix operands and complex multiplication for scalar operands. Matrix.conjTranspose is conjugate transpose.")),
                Paragraph(Text(
                    "Matrix.IsHermitian means equality with the conjugate transpose. Matrix.PosSemidef "
                        + "includes Hermitian symmetry and nonnegativity of the quadratic form on every "
                        + "finitely supported complex vector. The inequality uses the complex order.")),
                Display(HermitianFormula()),
                Display(PosSemidefFormula()),
                Paragraph(Text(
                    "The channel predicate is finite Kraus form with identity normalization. The input "
                        + "and output index types are finite with decidable equality; no condition on an "
                        + "individual input matrix is imposed. Bracketed Fintype and DecidableEq assumptions are anonymous typeclass assumptions.")),
                Display(ChannelFormula()),
                Paragraph(Text(
                    "The two partial traces of a joint output sum over its first and second coordinates, respectively.")),
                Display(PartialTraceFormula(true)),
                Display(PartialTraceFormula(false)),
                Paragraph(Text(
                    "LinearMap.id acts as the identity on every input matrix. MatrixMap.kron acts on "
                        + "matrix units by the following finite sum, with both maps complex linear. "
                        + "The displayed specializations have the same input and output index type in each factor. "
                        + "Bracketed Fintype and DecidableEq assumptions are anonymous typeclass assumptions.")),
                Display(IdentityFormula()),
                Display(KronFormula()),
                Paragraph(Text(
                    "MatrixMap.choi_matrix uses output-first indices. For LinearMap.id its entries "
                        + "are those of the matrix unit with the second pair of coordinates as labels. "
                        + "This is the operator in equation (117), equivalently equation (120).")),
                Display(ChoiIdentityFormula()))),
            Node("traceX1", "Tracing out the middle input factor", TraceFormula(true),
                "Definition 25, equation (117): traceX1 sums the middle coordinate of the three-factor matrix and retains the reference and last coordinates.",
                AssessedProvenance.FromLiterature(Source)),
            Node("traceX2", "Tracing out the last input factor", TraceFormula(false),
                "Definition 25, equation (117): traceX2 sums the last coordinate and retains the reference and middle coordinates.",
                AssessedProvenance.FromLiterature(Source)),
            Node("jordanAction", "The Choi matrix of the generalized Jordan product", JordanActionFormula(),
                "Definition 25, equation (119): apply the identity to the reference factor and the two maps to the other factors. This operation is defined on every matrix A; Hermitian symmetry and the two marginal equations enter JordanCompatible separately.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Compatible", "A joint channel with the prescribed marginals", CompatibleFormula(),
                "Compatibility means that a channel into the product output space has the two prescribed partial traces on every complex input matrix. The predicate itself requires the joint map to be a channel; the channel assumptions on the two given maps are explicit in claim.",
                AssessedProvenance.FromLiterature(Source)),
            Node("JordanCompatible", "A Hermitian operator with positive Jordan image", JordanCompatibleFormula(),
                "Definition 27 requires a Hermitian A satisfying both equations (117), whose generalized Jordan product is completely positive. By the Choi criterion this is positive semidefiniteness of jordanAction. A itself need not be positive semidefinite. Proposition 26 gives compatibility from these conditions for channels.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture following Theorem 30", ClaimFormula(),
                "For every natural dimension and every pair of channels on that matrix space, compatibility implies Jordan compatibility. Theorem 30 proves this implication when both channels have inverse linear maps. The conjecture after its proof removes that invertibility hypothesis; claim states precisely this unrestricted implication.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("jordan-compatibility-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A compatible pair in dimension four"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let P interchange the first and third standard basis vectors and the second and fourth, "
                            + "and let Q = diag(1,1,−1,−1). Both are real symmetric involutions and PQ + QP = 0. "
                            + "Put (S₁,S₂,S₃,S₄) = (P,−P,Q,−Q), Eᵢ = (5I + 4Sᵢ)/20 and Fⱼ = (4I + 3Sⱼ)/16. "
                            + "These positive semidefinite effects each sum to I. The two channels send R to "
                            + "diag(tr(EᵢR)) and diag(tr(FⱼR)). The joint channel sends R to the diagonal matrix "
                            + "with entries hᵢⱼ tr(EᵢR), where hᵢⱼ = 1/64 + (15/16)δᵢⱼ and δᵢⱼ is one "
                            + "when i = j and zero otherwise. Its two partial traces are the two channels.")),
                    Paragraph(Text(
                        "Suppose A satisfies the two marginal equations and its Jordan image is positive semidefinite. "
                            + "The diagonal output blocks are positive semidefinite matrices. Multiply the four blocks "
                            + "with first output in {1,2} and second output in {3,4} by four, and label them Gₛₜ "
                            + "for s,t in {1,−1}. Their total is I, their s-weighted sum is (4/5)P, and their "
                            + "t-weighted sum is (3/4)Q. For Hₛₜ = (3/2)I − sP − tQ, the identity "
                            + "Hₛₜ = (1/4)(2I − sP − tQ)†(2I − sP − tQ) makes every Hₛₜ positive semidefinite. "
                            + "Consequently the sum of the real parts of tr(HₛₜGₛₜ) is at least zero. "
                            + "The three moment identities make the same sum equal to 6 − 16/5 − 3 = −1/5, "
                            + "a contradiction. Thus these compatible channels are not Jordan compatible."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girard-plavala-sikora-2021-jordan-compatibility-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("jordan-compatibility-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Display(Formula formula) => new DocumentBlock.DisplayFormula(formula);

    private static Formula MatFormula() => All("ι", TypeStar(),
        Equal(Mat(V("ι")), Matrix(V("ι"), V("ι"))));

    private static Formula MapFormula() => All("ι", TypeStar(), All("κ", TypeStar(),
        Equal(Map(V("ι"), V("κ")),
            At(Op(MatrixMaps), V("ι"), V("κ"), Complex()))));

    private static Formula HermitianFormula() => All("ι", TypeStar(), All("M", Mat(V("ι")),
        Equivalence(At(Op("Matrix.IsHermitian"), V("M")),
            Equal(At(Op("Matrix.conjTranspose"), V("M")), V("M")))));

    private static Formula PosSemidefFormula()
    {
        Formula inner = At(Op("Finsupp.sum"), V("x"),
            LambdaOf("j", V("ι"), LambdaOf("xj", Complex(),
                Multiply(Multiply(At(Op("Star.star"), V("xi")), At(V("M"), V("i"), V("j"))), V("xj")))));
        Formula quadratic = At(Op("Finsupp.sum"), V("x"),
            LambdaOf("i", V("ι"), LambdaOf("xi", Complex(), inner)));
        return All("ι", TypeStar(), All("M", Mat(V("ι")),
            Equivalence(At(Op("Matrix.PosSemidef"), V("M")),
                And(At(Op("Matrix.IsHermitian"), V("M")),
                    All("x", At(Op("Finsupp"), V("ι"), Complex()), LE(D(0), quadratic))))));
    }

    private static Formula ChannelFormula()
    {
        Formula k = At(V("K"), V("k"));
        Formula adjoint = At(Op("Matrix.conjTranspose"), k);
        Formula gram = SumOver("k", Fin(V("r")), Multiply(adjoint, k));
        Formula action = SumOver("k", Fin(V("r")), Multiply(Multiply(k, V("R")), adjoint));
        Formula body = All("T", Arrow(Mat(V("α")), Mat(V("β"))),
            Equivalence(At(Op(Channel), V("T")),
                Ex("r", Naturals(), Ex("K", Arrow(Fin(V("r")), Matrix(V("β"), V("α"))),
                    And(Equal(gram, Typed(D(1), Mat(V("α")))),
                        All("R", Mat(V("α")), Equal(At(V("T"), V("R")), action)))))));
        return FiniteTypes(body);
    }

    private static Formula PartialTraceFormula(bool left)
    {
        Formula entry = left
            ? At(V("R"), Pair(V("r"), V("p")), Pair(V("r"), V("q")))
            : At(V("R"), Pair(V("p"), V("r")), Pair(V("q"), V("r")));
        return All("d", Naturals(), All("R", Mat(Product(FinD(), FinD())),
            All("p", FinD(), All("q", FinD(),
                Equal(At(At(Op(PartialTraces + (left ? ".partialTraceLeft" : ".partialTraceRight")), V("R")),
                    V("p"), V("q")), SumOver("r", FinD(), entry))))));
    }

    private static Formula IdentityFormula() => All("d", Naturals(), All("R", Mat(FinD()),
        Equal(At(Identity(), V("R")), V("R"))));

    private static Formula KronFormula()
    {
        Formula coefficient = Multiply(
            At(V("T"), At(Op("Matrix.single"), V("i"), V("j"), D(1)), V("a"), V("b")),
            At(V("U"), At(Op("Matrix.single"), V("k"), V("l"), D(1)), V("c"), V("e")));
        Formula sum = SumOver("i", V("α"), SumOver("j", V("α"),
            SumOver("k", V("β"), SumOver("l", V("β"),
                Multiply(coefficient, At(V("R"), Pair(V("i"), V("k")), Pair(V("j"), V("l"))))))));
        Formula body = All("T", Map(V("α"), V("α")), All("U", Map(V("β"), V("β")),
            All("R", Mat(Product(V("α"), V("β"))),
                All("a", V("α"), All("b", V("α"), All("c", V("β"), All("e", V("β"),
                    Equal(At(At(Op(MatrixMaps + ".kron"), V("T"), V("U")), V("R"),
                        Pair(V("a"), V("c")), Pair(V("b"), V("e"))), sum))))))));
        return FiniteTypes(body);
    }

    private static Formula ChoiIdentityFormula()
    {
        Formula entry = At(At(Op("Matrix.single"), Component("p", 2), Component("q", 2), D(1)),
            Component("p", 1), Component("q", 1));
        Formula condition = And(Equal(Component("p", 1), Component("p", 2)),
            Equal(Component("q", 1), Component("q", 2)));
        Formula cases = Seq(Op("if"), Sp, Parenthesized(condition), Sp, Op("then"), Sp,
            D(1), Sp, Op("else"), Sp, D(0));
        return All("d", Naturals(), All("p", Product(FinD(), FinD()),
            All("q", Product(FinD(), FinD()),
                And(Equal(At(ChoiIdentity(), V("p"), V("q")), entry), Equal(entry, cases)))));
    }

    private static Formula TraceFormula(bool middle)
    {
        Formula row = middle ? Pair(Component("p", 1), Pair(V("r"), Component("p", 2)))
            : Pair(Component("p", 1), Pair(Component("p", 2), V("r")));
        Formula column = middle ? Pair(Component("q", 1), Pair(V("r"), Component("q", 2)))
            : Pair(Component("q", 1), Pair(Component("q", 2), V("r")));
        return All("d", Naturals(), All("A", Mat(TripleIndex()),
            Equal(LocalCall(middle ? "traceX1" : "traceX2", V("A")),
                LambdaOf("p", Product(FinD(), FinD()), LambdaOf("q", Product(FinD(), FinD()),
                    SumOver("r", FinD(), At(V("A"), row, column)))))));
    }

    private static Formula JordanActionFormula() => MapBinders(All("A", Mat(TripleIndex()),
        Equal(LocalCall("jordanAction", V("Φ"), V("Ψ"), V("A")),
            At(At(Op(MatrixMaps + ".kron"), Identity(),
                At(Op(MatrixMaps + ".kron"), V("Φ"), V("Ψ"))), V("A")))));

    private static Formula CompatibleFormula()
    {
        Formula right = All("R", Mat(FinD()),
            Equal(At(Op(PartialTraces + ".partialTraceRight"), At(V("Γ"), V("R"))), At(V("Φ"), V("R"))));
        Formula left = All("R", Mat(FinD()),
            Equal(At(Op(PartialTraces + ".partialTraceLeft"), At(V("Γ"), V("R"))), At(V("Ψ"), V("R"))));
        return MapBinders(Equivalence(LocalCall("Compatible", V("Φ"), V("Ψ")),
            Ex("Γ", Map(FinD(), Product(FinD(), FinD())),
                And(At(Op(Channel), V("Γ")), And(right, left)))));
    }

    private static Formula JordanCompatibleFormula() => MapBinders(
        Equivalence(LocalCall("JordanCompatible", V("Φ"), V("Ψ")),
            Ex("A", Mat(TripleIndex()), And(At(Op("Matrix.IsHermitian"), V("A")),
                And(Equal(LocalCall("traceX1", V("A")), ChoiIdentity()),
                    And(Equal(LocalCall("traceX2", V("A")), ChoiIdentity()),
                        At(Op("Matrix.PosSemidef"), LocalCall("jordanAction", V("Φ"), V("Ψ"), V("A")))))))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"),
        MapBinders(Imp(At(Op(Channel), V("Φ")), Imp(At(Op(Channel), V("Ψ")),
            Imp(LocalCall("Compatible", V("Φ"), V("Ψ")),
                LocalCall("JordanCompatible", V("Φ"), V("Ψ")))))));

    private static Formula V(string name) => name switch
    {
        "ι" => F.Id("iota"),
        "κ" => Kappa,
        "α" => Alpha,
        "β" => Beta,
        "Φ" => Phi,
        "Ψ" => Psi,
        "Γ" => Gamma,
        _ => F.Id(name)
    };
    private static Formula Op(string name)
    {
        var parts = name.Split('.');
        Formula result = NamePart(parts[0]);
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, NamePart(part));
        return result;
    }
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = Seq(Operatorname, Grp(V(words[0])));
        foreach (var word in words.Skip(1))
            result = Seq(result, Underscore, Grp(V(word)));
        return result;
    }
    private static Formula Local(string name) => Op("D5.S3.QuantumChannels.JordanCompatibilityRefutation." + name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula TypeStar() => Seq(Op("Type"), Star);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula size) => At(Op("Fin"), size);
    private static Formula FinD() => Fin(V("d"));
    private static Formula Mat(Formula index) => At(Local("Mat"), index);
    private static Formula Matrix(Formula rows, Formula columns) => At(Op("Matrix"), rows, columns, Complex());
    private static Formula Map(Formula input, Formula output) => At(Local("Map"), input, output);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula TripleIndex() => Product(FinD(), Product(FinD(), FinD()));
    private static Formula Component(string name, byte index) => Seq(V(name), Dot, D(index));
    private static Formula Identity() => Typed(Op("LinearMap.id"), Map(FinD(), FinD()));
    private static Formula ChoiIdentity() => At(Op(MatrixMaps + ".choi_matrix"), Identity());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula MapBinders(Formula body) => All("d", Naturals(),
        All("Φ", Map(FinD(), FinD()), All("Ψ", Map(FinD(), FinD()), body)));
    private static Formula FiniteTypes(Formula body) => All("α", Op("Type"), All("β", Op("Type"),
        Seq(Seq(OpenBracket, At(Op("Fintype"), V("α")), CloseBracket), Sp,
            Seq(OpenBracket, At(Op("DecidableEq"), V("α")), CloseBracket), Sp,
            Seq(OpenBracket, At(Op("Fintype"), V("β")), CloseBracket), Sp,
            Seq(OpenBracket, At(Op("DecidableEq"), V("β")), CloseBracket), Sp,
            Parenthesized(body))));
}
