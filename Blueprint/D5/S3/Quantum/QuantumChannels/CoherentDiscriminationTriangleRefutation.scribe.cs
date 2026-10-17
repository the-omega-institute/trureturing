using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class CoherentDiscriminationTriangleRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/wilde2020coherentdiscrimination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent discrimination bias fails the triangle inequality for three qubit replacement channels.",
        H("Coherent discrimination bias is not a channel metric"), Blocks(
            Paragraph(Text(
                "The input A, output B and flag F have basis Fin(2); the four Kraus operators are indexed by Fin(4). "
                    + "Fin(n) consists of the integers from 0 to n − 1. Matrices and vectors have complex entries. "
                    + "Matrix.unitaryGroup consists of unitary matrices, and a dagger denotes conjugate transpose. "
                    + "A finite reference R is retained throughout the experiment. The finite ancilla E, representing E′, "
                    + "has a specified zero state e₀, denoted e in the formulas. Products of types index tensor-product bases. "
                    + "Prod.fst and Prod.snd select the first and second coordinates of a pair; tuples are nested to the right. "
                    + "The anonymous brackets supply finite enumerations and decidable equality. All finite sums include every index.")),
            Node("extend", "The canonical isometric extension", ExtensionFormula(),
                "For a Kraus family K, the vector extend(K, ψ) has coordinate (r,b,k) equal to "
                    + "the sum over a of K_k(b,a) ψ(r,a). This is the canonical extension of Eq. (10), "
                    + "with the reference coordinate unchanged. The formula is defined for every K and ψ. "
                    + "For a channel, the Kraus normalization is the matrix identity Σ_k K_k† K_k = 1; "
                    + "under this condition the extension is an isometry. The identity matrix acts on the input qubit."),
            Node("successProbability", "Success of a coherent discrimination strategy", SuccessFormula(),
                "Equation (17) adjoins the basis states e₀ and 0 of E′ and F, applies the prover's unitary V "
                    + "on R, B, E′ and F while retaining the Kraus index, and applies the adjoint extension. "
                    + "For the first channel the final flag is 0; for the second it is 1. "
                    + "The sum over i adds the two resulting vectors on R, A and E′ coherently, "
                    + "using K when i = 0 and L when i = 1. "
                    + "Their squared Euclidean norm is the sum of squared complex moduli displayed here. "
                    + "The factor 1/4 is the initial factor 1/2 in Eq. (17) multiplied by the factor 1/2 "
                    + "from contraction with the normalized Bell bra. The conditional inserts the two initial zero states. "
                    + "For a physical strategy ψ is a unit vector and the Kraus families satisfy the normalization "
                    + "Σ_k K_k† K_k = 1. The expression itself is defined for arbitrary ψ and Kraus matrices."),
            Node("coherentValue", "The optimal coherent success probability", ValueFormula(),
                "Equation (18) takes the real supremum over every finite reference R, finite pointed ancilla E′, "
                    + "unit input ψ on R and A, and prover unitary V on R, B, E′ and F. "
                    + "The set explicitly includes every such choice of finite types in Type and its instances. "
                    + "For normalized Kraus families this is p_s^coh. The source states after Eq. (17) "
                    + "that its value is independent of the chosen isometric extensions. "
                    + "No normalization condition on the Kraus matrices is imposed by this definition alone."),
            Node("claim", "The proposed triangle inequality", ClaimFormula(),
                "Put d(N,M) = p_s^coh(N,M) − 1/2. The assertion requires the triangle inequality "
                    + "for every three qubit channels represented by four Kraus operators each. "
                    + "Each displayed normalization Σ_k K_k† K_k = 1 is exactly the channel condition. "
                    + "Section VI asks whether p_s^coh − 1/2 is a metric on quantum channels. "
                    + "That metric property implies this triangle inequality, because the optimal value "
                    + "is independent of the choice of isometric extensions."),
            Describe.Lean(
                DescribeId.Create("coherent-discrimination-triangle-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Three replacement channels violate the triangle inequality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a strictly positive probability vector t = (t₀,t₁), consider the qubit channel "
                            + "R_t(X) = Tr(X) diag(t₀,t₁). Its four Kraus operators are √t_j |j⟩⟨k|, "
                            + "with j,k in Fin(2), indexed by the equivalence Fin(2) × Fin(2) ≃ Fin(4). "
                            + "Their conjugate-transpose products sum to the identity.")),
                    Paragraph(Text(
                        "For two such vectors t,u, set s_j = √(t_j² + u_j²). Then "
                            + "p_s^coh(R_t,R_u) = (s₀ + s₁)²/4. To obtain the upper bound, fix any strategy "
                            + "and write Q_ij for the part of V from (B = j, E′ = e₀, F = 0) "
                            + "to (B = j, F = i): explicitly, "
                            + "(Q_ij ψ)(r,a,e′) = Σ_q V((r,j,e′,i),(q,j,e₀,0)) ψ(q,a). "
                            + "Unitarity gives ‖Q_0j ψ‖² + ‖Q_1j ψ‖² ≤ ‖ψ‖². "
                            + "The vector in the success expression is Σ_j (t_j Q_0j + u_j Q_1j) ψ. "
                            + "Cauchy–Schwarz bounds each summand's norm by s_j ‖ψ‖, "
                            + "and the triangle inequality gives the probability bound (s₀ + s₁)²/4.")),
                    Paragraph(Text(
                        "Equality is attained with trivial reference and ancilla, input |0⟩, "
                            + "and the unitary that, conditioned on B = j, acts on F by "
                            + "(1/s_j)[[t_j,−u_j],[u_j,t_j]]. Its two relevant entries are t_j/s_j "
                            + "and u_j/s_j, so their weighted sum is s_j. Thus the upper bound "
                            + "belongs to the set of strategy values and is its supremum.")),
                    Paragraph(Text(
                        "Take t = (3/4,1/4), u = (1/2,1/2), and v = (1/4,3/4). "
                            + "The closed form gives p_s^coh(R_t,R_v) = 5/8 and "
                            + "p_s^coh(R_t,R_u) = p_s^coh(R_u,R_v) = (9 + √65)/32. "
                            + "Consequently d(R_t,R_v) = 1/8, whereas "
                            + "d(R_t,R_u) = d(R_u,R_v) = (√65 − 7)/32. "
                            + "Their sum (√65 − 7)/16 is strictly less than 1/8 because √65 < 9. "
                            + "These normalized Kraus families contradict claim and hence give a negative "
                            + "answer to the metric question in Section VI."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wilde-2020-coherent-discrimination-triangle-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("coherent-discrimination-triangle-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(N(part)));
        }
        return Seq([.. items]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula QubitMatrices() => Call("Matrix", Fin(2), Fin(2), N("Complex"));
    private static Formula KrausFamilies() => Arrow(Fin(4), QubitMatrices());
    private static Formula InputType() => Product(N("R"), Fin(2));
    private static Formula VectorType() => Product(N("R"), Product(Fin(2), N("E")));
    private static Formula ProverType() => Product(N("R"), Product(Fin(2), Product(N("E"), Fin(2))));
    private static Formula Unitaries() => Call("Matrix.unitaryGroup", ProverType(), N("Complex"));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, type)), Parenthesized(body));
    private static Formula NormSquared(Formula vector) => new Formula.Power(new Formula.Norm(vector), D(2));
    private static Formula First(Formula pair) => Call("Prod.fst", pair);
    private static Formula Second(Formula pair) => Call("Prod.snd", pair);

    private static Formula ExtensionFormula()
    {
        var coordinate = Equal(
            At(Call("extend", N("K"), N("psi")), Pair(N("r"), Pair(N("b"), N("k")))),
            SumOver("a", Fin(2), Multiply(At(N("K"), N("k"), N("b"), N("a")),
                At(N("psi"), Pair(N("r"), N("a"))))));
        return All("R", N("Type"), All("K", KrausFamilies(),
            All("psi", Arrow(InputType(), N("Complex")),
                All("r", N("R"), All("b", Fin(2), All("k", Fin(4), coordinate))))));
    }

    private static Formula Instances(Formula body) =>
        Instance(Call("Fintype", N("R")), Instance(Call("Fintype", N("E")),
            Instance(Call("DecidableEq", N("R")), Instance(Call("DecidableEq", N("E")), body))));

    private static Formula Uncomputed(Formula family, Formula flag)
    {
        var x = N("x");
        var y = N("y");
        var initial = Seq(Q("if"), Sp, Parenthesized(And(
            Equal(First(Second(Second(y))), N("e")), Equal(Second(Second(Second(y))), D(0)))),
            Sp, Q("then"), Sp,
            At(Call("extend", family, N("psi")), Pair(First(y), Pair(First(Second(y)), N("k")))),
            Sp, Q("else"), Sp, D(0));
        var entry = At(Call("Subtype.val", N("V")),
            Pair(First(x), Pair(N("b"), Pair(Second(Second(x)), flag))), y);
        return SumOver("b", Fin(2), SumOver("k", Fin(4),
            Multiply(Call("conj", At(family, N("k"), N("b"), First(Second(x)))),
                SumOver("y", ProverType(), Multiply(entry, Parenthesized(initial))))));
    }

    private static Formula SuccessFormula()
    {
        var family = Parenthesized(Seq(Q("if"), Sp, Parenthesized(Equal(N("i"), D(0))),
            Sp, Q("then"), Sp, N("K"), Sp, Q("else"), Sp, N("L")));
        var probability = Equal(Call("successProbability", N("K"), N("L"), N("psi"), N("V"), N("e")),
            Multiply(new Formula.Fraction(D(1), D(4)), SumOver("x", VectorType(),
                NormSquared(SumOver("i", Fin(2), Uncomputed(family, N("i")))))));
        var strategy = All("psi", Arrow(InputType(), N("Complex")),
            All("V", Unitaries(), All("e", N("E"), probability)));
        return All("R", N("Type"), All("E", N("Type"),
            Instances(All("K", KrausFamilies(), All("L", KrausFamilies(), strategy)))));
    }

    private static Formula ValueFormula()
    {
        var unitInput = Equal(SumOver("x", InputType(), NormSquared(At(N("psi"), N("x")))), D(1));
        var value = Equal(N("p"), Call("successProbability", N("K"), N("L"), N("psi"), N("V"), N("e")));
        var choices = Some("e", N("E"), Some("psi", Arrow(InputType(), N("Complex")),
            Some("V", Unitaries(), And(unitInput, value))));
        var strategies = Some("R", N("Type"), Some("E", N("Type"), Instances(choices)));
        var values = Seq(OpenBrace, N("p"), Colon, N("Real"), Bar, strategies, CloseBrace);
        return All("K", KrausFamilies(), All("L", KrausFamilies(),
            Equal(Call("coherentValue", N("K"), N("L")), Call("sSup", values))));
    }

    private static Formula Normalized(Formula family) => Equal(
        SumOver("k", Fin(4), Multiply(Call("Matrix.conjTranspose", At(family, N("k"))), At(family, N("k")))), D(1));
    private static Formula Bias(Formula first, Formula second) =>
        Subtract(Call("coherentValue", first, second), new Formula.Fraction(D(1), D(2)));
    private static Formula ClaimFormula()
    {
        var triangle = LessEqual(Bias(N("K"), N("M")), Add(
            Parenthesized(Bias(N("K"), N("L"))), Parenthesized(Bias(N("L"), N("M")))));
        var channels = Implies(Normalized(N("K")),
            Implies(Normalized(N("L")), Implies(Normalized(N("M")), triangle)));
        return IffFormula(N("claim"), All("K", KrausFamilies(),
            All("L", KrausFamilies(), All("M", KrausFamilies(), channels))));
    }
}
