using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class WallmanFlammiaTwoContractivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wallmanflammia2014confidence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonunitary channel is two-contractive under a finite exact unitary two-design.",
        H("Wallman–Flammia two-contractivity"), Blocks(
            Node("isunitarytwodesign", "Exact second unitary moment", TwoDesignDefinition(),
                "Section II, PDF page 2: “we require G to be a unitary 2-design (e.g., the Clifford group on n qubits for d=2ⁿ), meaning that sampling over G reproduces the second moments of the Haar measure”. The finite subgroup carries its uniform distribution. HaarTwoCopyTwirl.literalMoment orders the four factors as two conjugate matrices followed by two original matrices.",
                "IsUnitaryTwoDesign", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjugatedentry", "A matrix entry of the conjugated channel", EntryDefinition(),
                "Section IV.A, PDF page 8: “Given a rep (φ,V) of a group G, a matrix A∈GL(V) and an element g∈G, we define Aᵍ = φ(g)Aφ(g⁻¹).” Matrix.single supplies the input matrix unit; the row and column indices each range over Fin d × Fin d. The channel acts on the entire complex matrix space.",
                "conjugatedEntry", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("twirledtensorpower", "Uniform tensor-power twirl", TensorDefinition(),
                "Section IV.A, PDF page 8: “The uniform average of this action on A is called the G-twirl of A, and is given by Aᴳ = |G|⁻¹∑g∈G Aᵍ.” The n tensor factors are indexed by Fin n. Their matrix-unit entries are multiplied before the uniform average is taken.",
                "twirledTensorPower", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isncontractive", "Definition 15", ContractiveDefinition(),
                "Definition 15, PDF page 23: “A channel Λ:Dd → Dd is n-contractive with respect to a group G⊆U(d) if (Λ⊗n)ᴳ has at most one eigenvalue of modulus 1.” The roots of the characteristic polynomial form a multiset, so the count includes algebraic multiplicity.",
                "IsNContractive", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture before Proposition 16", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "Section VII, PDF page 24: “We conjecture that all nonunitary channels are in fact 2-contractive with respect to any unitary 2-design.” The dimension is any natural number at least two. QuantumChannel supplies complete positivity and trace preservation. The subgroup is finite, its second moment is exact, and no unitary conjugation agrees with the channel on every input matrix.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Unrestricted two-contractivity", Disp(ClaimBody()),
                "The second moment makes both averaged Gram matrices scalar multiples of the traceless projection. A rectangular factorization bounds the full traceless tensor square, including complex non-Hermitian directions. Choi purity makes the scalar strictly less than one for every nonunitary channel. In trace-adapted coordinates the four diagonal tensor sectors are the scalar identity, two strictly contractive one-copy blocks, and the strictly contractive traceless tensor square. Their characteristic polynomials leave exactly one root on the unit circle. The nonunital entries occupy lower blocks and do not change this factorization.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wf1404"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula TwoDesignDefinition() => Disp(All("d", N,
        All("G", Group(V("d")), Instance("Fintype", V("G"),
            Equal(Call("IsUnitaryTwoDesign", V("G")),
                Equal(QCall("HSMul", "hSMul", Inverse(Cast(Card(V("G")), C)),
                    SumOver("g", V("G"), QCall("D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl", "literalMoment", Val(Val(V("g")))))),
                    QCall("D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl", "haarAverage", Fin(V("d")))))))));

    private static Formula EntryDefinition()
    {
        var u = Val(V("U"));
        var input = QCall("Matrix", "single", Field(V("c"), D(1)), Field(V("c"), D(2)), D(1));
        var conjugated = Product(Product(u, Action(Product(Product(Adjoint(u), input), u))), Adjoint(u));
        var entry = App(conjugated, Field(V("r"), D(1)), Field(V("r"), D(2)));
        return Disp(All("d", N, All("Lambda", Channel(V("d")), All("U", Unitary(V("d")),
            All("r", Index(V("d")), All("c", Index(V("d")),
                Equal(Call("conjugatedEntry", V("Lambda"), V("U"), V("r"), V("c")), entry)))))));
    }

    private static Formula TensorDefinition()
    {
        var entry = Call("conjugatedEntry", V("Lambda"), Val(V("g")),
            App(V("r"), V("k")), App(V("c"), V("k")));
        var average = Product(Inverse(Cast(Card(V("G")), C)),
            SumOver("g", V("G"), ProdOver("k", Fin(V("n")), entry)));
        var body = Fun("r", Arrow(Fin(V("n")), Index(V("d"))),
            Fun("c", Arrow(Fin(V("n")), Index(V("d"))), average));
        return Disp(All("d", N, All("Lambda", Channel(V("d")), All("G", Group(V("d")),
            Instance("Fintype", V("G"), All("n", N,
                Equal(Call("twirledTensorPower", V("Lambda"), V("G"), V("n")), body)))))));
    }

    private static Formula ContractiveDefinition() => Disp(All("d", N, All("Lambda", Channel(V("d")),
        All("G", Group(V("d")), Instance("Fintype", V("G"), All("n", N,
            Equal(Call("IsNContractive", V("Lambda"), V("G"), V("n")),
                LE(QCall("Multiset", "card", QCall("Multiset", "filter",
                    Fun("z", C, Equal(new Formula.Norm(V("z")), D(1))),
                    QCall("Polynomial", "roots", QCall("Matrix", "charpoly",
                        Call("twirledTensorPower", V("Lambda"), V("G"), V("n")))))), D(1)))))))));

    private static Formula ClaimBody() => All("d", N, Imp(LE(D(2), V("d")),
        All("Lambda", Channel(V("d")), All("G", Group(V("d")), Instance("Fintype", V("G"),
            Imp(Call("IsUnitaryTwoDesign", V("G")), Imp(Not(
                ExistsIn("U", Unitary(V("d")), All("X", Mat(V("d")),
                    Equal(Action(V("X")), Product(Product(Val(V("U")), V("X")), Adjoint(Val(V("U")))))))),
                Call("IsNContractive", V("Lambda"), V("G"), D(2)))))))));

    private static Formula Action(Formula x) => App(Field(Q("CStarMatrix", "ofMatrix"), V("symm")),
        App(Field(V("Lambda"), V("toCompletelyPositiveMap")), QCall("CStarMatrix", "ofMatrix", x)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in (owner + "." + name).Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(Named(part));
        }
        return Seq([..tokens]);
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Q(owner, name), args);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Field(Formula value, Formula field) => Seq(Parenthesized(value), Dot, field);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProdOver(string name, Formula type, Formula body) =>
        Seq(Prod, Underscore, Grp(Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Product(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Inverse(Formula a) => new Formula.Power(Parenthesized(a), Seq(Minus, D(1)));
    private static Formula Adjoint(Formula a) => QCall("Matrix", "conjTranspose", a);
    private static Formula Card(Formula a) => QCall("Fintype", "card", a);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Index(Formula d) => Seq(Fin(d), Sp, Times, Sp, Fin(d));
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), C);
    private static Formula Unitary(Formula d) => QCall("Matrix", "unitaryGroup", Fin(d), C);
    private static Formula Group(Formula d) => Call("Subgroup", Unitary(d));
    private static Formula Channel(Formula d) => Call("QuantumChannel", Fin(d), Fin(d));
}
