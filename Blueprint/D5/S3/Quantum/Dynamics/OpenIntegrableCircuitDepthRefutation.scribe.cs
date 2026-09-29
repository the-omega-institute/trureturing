using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OpenIntegrableCircuitDepthRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/garciafernandez2026openqc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjectures 1 and 2 of Garcia Fernandez, Paletta and Retore on the minimum depth of open-boundary integrable quantum circuits are false: with eight sites and two sites carrying -kappa the configuration (6, 3) runs in three layers, one fewer than conjectured, and with eleven sites the configuration (8, 4) runs in four, one fewer than conjectured.",
        H("The conjectured minimum depths of open integrable circuits are false"),
        Blocks(
            Node("gate", "Gates", GateFormula(),
                "The two-site gate U_j acts on the sites j and j + 1, the boundary gate K1 on site 1 and the boundary gate KN on site N.",
                "sites", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("circuit", "The circuit of a configuration", CircuitFormula(),
                "The circuit of Theorems 1 and 2 for the set S of sites carrying -kappa, listed in time order, the rightmost factor of the operator product first. When N is not in S the boundary gate KN acts first, then U_j for the sites j < N outside S in decreasing order, then K1, then U_n for n in S in increasing order; when N is in S, KN acts last and U_N is omitted.",
                "circuit", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("runs", "Layerings", RunsFormula(),
                "A list of gates fits in L layers when some layer map below L keeps the time order of every two gates that act on a common site in the chain of N sites; gates on disjoint sites may share a layer.",
                "RunsIn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("depth", "Depth", Disp(Equal(Call("depth", F.Id("N"), F.Id("w")),
                Seq(Named("inf"), Sp, OpenBrace, F.Id("L"), Sp, Mid, Sp, Call("RunsIn", F.Id("N"), F.Id("w"), F.Id("L")), CloseBrace))),
                "The least number of layers a circuit fits in.",
                "depth", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mindepth", "Minimum depth", MinDepthFormula(),
                "The least depth over the configurations of kappa sites among 1, ..., N.",
                "minDepth", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjone", "Conjecture 1", ConjFormula("conjectureOne", "Odd", F.Id("N"), D(3), true),
                "For odd N and 0 < kappa <= (N - 1)/2 the minimum depth is (N + 3)/2 - kappa.",
                "conjectureOne", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjtwo", "Conjecture 2", ConjFormula("conjectureTwo", "Even", F.Id("N"), D(4), false),
                "For even N and 0 < kappa <= N/2 the minimum depth is (N + 4)/2 - kappa.",
                "conjectureTwo", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Either conjecture", Disp(Iff(F.Id("claim"), Or(F.Id("conjectureOne"), F.Id("conjectureTwo")))),
                "At least one of the two conjectures holds; the result refutes both.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "For N = 8 and S = {3, 6} the circuit is KN, U7, U5, U4, U2, U1, K1, U3, U6 in time order, and the layers 0, 1, 0, 1, 0, 1, 2, 2, 2 keep the order of every two gates sharing a site, so its depth is at most 3 and the minimum depth for two sites is at most 3, while Conjecture 2 gives (8 + 4)/2 - 2 = 4. For N = 11 and S = {4, 8} the circuit is KN, U10, U9, U7, U6, U5, U3, U2, U1, K1, U4, U8 with the layers 0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 3, 3, so the minimum depth for two sites is at most 4, while Conjecture 1 gives (11 + 3)/2 - 2 = 5. Both layer maps are checked by the kernel.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garcia-fernandez-2026-open-circuit-min-depth-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("openqc-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Half(Formula value) => new Formula.Floor(new Formula.Fraction(value, D(2)));

    private static Formula GateFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j");
        return Disp(Seq(
            Equal(Call("sites", n, Call("U", j)), new Formula.SetLiteral([j, Add(j, D(1))])), Comma, Quad,
            Equal(Call("sites", n, F.Id("K1")), new Formula.SetLiteral([D(1)])), Comma, Quad,
            Equal(Call("sites", n, F.Id("KN")), new Formula.SetLiteral([n]))));
    }

    private static Formula CircuitFormula()
    {
        Formula n = F.Id("N"), s = F.Id("S"), j = F.Id("j"), m = F.Id("n");
        Formula sites = Seq(OpenBrace, D(1), Comma, Sp, Named("dots"), Comma, Sp, Subtract(n, D(1)), CloseBrace);
        Formula down = Seq(Named("U"), Underscore, Grp(j), Sp,
            Parenthesized(Seq(Member(j, Seq(sites, Sp, Setminus, Sp, s)), Comma, Sp, Named("decreasing"))));
        Formula up = Seq(Named("U"), Underscore, Grp(m), Sp,
            Parenthesized(Seq(Member(m, s), Comma, Sp, Named("increasing"))));
        Formula upBelow = Seq(Named("U"), Underscore, Grp(m), Sp,
            Parenthesized(Seq(Member(m, Seq(s, Sp, Setminus, Sp, new Formula.SetLiteral([n]))), Comma, Sp, Named("increasing"))));
        Formula outside = Seq(Call("circuit", n, s), Sp, Eq, Sp, F.Id("KN"), Comma, Sp, down, Comma, Sp,
            F.Id("K1"), Comma, Sp, up, Quad, Parenthesized(new Formula.Not(Member(n, s))));
        Formula inside = Seq(Call("circuit", n, s), Sp, Eq, Sp, down, Comma, Sp,
            F.Id("K1"), Comma, Sp, upBelow, Comma, Sp, F.Id("KN"), Quad, Parenthesized(Member(n, s)));
        return Disp(Seq(outside, Comma, Quad, inside));
    }

    private static Formula RunsFormula()
    {
        Formula n = F.Id("N"), w = F.Id("w"), l = F.Id("L"), f = F.Id("f"), i = F.Id("i"), j = F.Id("j");
        Formula share = Ex("k", Naturals(), And(Member(F.Id("k"), Call("sites", n, Call("w", i))),
            Member(F.Id("k"), Call("sites", n, Call("w", j)))));
        Formula body = Ex("f", new Formula.TypeArrow(Naturals(), Naturals()),
            And(All("i", Naturals(), Implies(Less(i, Call("length", w)), Less(Call("f", i), l))),
                All("j", Naturals(), All("i", Naturals(), Implies(
                    And(And(Less(i, j), Less(j, Call("length", w))), share),
                    Less(Call("f", i), Call("f", j)))))));
        return Disp(Iff(Call("RunsIn", n, w, l), body));
    }

    private static Formula MinDepthFormula()
    {
        Formula n = F.Id("N"), k = F.Id("kappa"), s = F.Id("S");
        Formula set = Seq(OpenBrace, Call("depth", n, Call("circuit", n, s)), Sp, Mid, Sp,
            SubsetOf(s, new Formula.SetLiteral([D(1), Named("dots"), n])), Comma, Sp,
            Equal(new Formula.Absolute(s), k), CloseBrace);
        return Disp(Equal(Call("minDepth", n, k), Seq(Named("inf"), Sp, set)));
    }

    private static Formula ConjFormula(string name, string parity, Formula n, Formula offset, bool odd)
    {
        Formula k = F.Id("kappa");
        Formula bound = odd ? Half(Subtract(n, D(1))) : Half(n);
        Formula body = All("N", Naturals(), All("kappa", Naturals(), Implies(
            And(And(Call(parity, n), Less(D(0), k)), AtMost(k, bound)),
            Equal(Call("minDepth", n, k), Subtract(Half(Add(n, offset)), k)))));
        return Disp(Iff(F.Id(name), body));
    }
}
