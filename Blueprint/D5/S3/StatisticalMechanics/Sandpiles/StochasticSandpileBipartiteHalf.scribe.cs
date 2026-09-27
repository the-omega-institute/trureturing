using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Sandpiles;

internal sealed class StochasticSandpileBipartiteHalfDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/alofi2024lackingbipartite");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the stochastic sandpile model on the complete bipartite graph K_{m,n}, m at least 2 and n at least 1, with the sink in the first part, the stochastically recurrent states number at most half of the n^(m-1) m^n stable configurations, and exactly half if and only if m = 2. This answers Question 6 of Alofi and Dukes: the stochastically recurrent states never dominate the stable states.",
        H("Stochastically recurrent states of K_{m,n} are at most half of the stable configurations"),
        Blocks(
            Node("orientation", "Orientations", OrientationFormula(),
                "An orientation of G directs every edge one way: O(u, v) = true means that the edge uv points from u to v, and then O(v, u) = false.",
                "IsOrientation", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("indeg", "In-degree", IndegFormula(),
                "in_O(v) is the number of edges directed into v.",
                "indeg", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stable", "Stable configurations", StableFormula(),
                "A stable configuration assigns to every non-sink vertex v a number of grains c(v) with 0 <= c(v) < d(v).",
                "Stable", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sto", "Stochastically recurrent states", StoFormula(),
                "Sto(G) is the set of stable configurations c compatible with some orientation O, that is with in_O(v) >= d(v) - c(v) at every non-sink vertex v (Definition 1 and Theorem 2 of the paper).",
                "Sto", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question 6", ClaimFormula(),
                "For m at least 2 and n at least 1, with K_{m,n} the complete bipartite graph on Fin m and Fin n and the sink the vertex 0 of the first part: twice the number of stochastically recurrent states is at most n^(m-1) m^n, with equality if and only if m = 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Answer", Disp(F.Id("claim")),
                "The vertices of the first part have degree n and those of the second part degree m, so there are n^(m-1) m^n stable configurations. Every orientation directs each of the mn edges into exactly one vertex, so the in-degrees sum to mn; summing in_O(v) + c(v) >= d(v) over the non-sink vertices of a stochastically recurrent c gives at least 2mn - n - mn = n(m - 1) grains. The involution c(v) -> d(v) - 1 - c(v) sends a configuration with S grains to one with (m - 1)(2n - 1) - S grains, so it maps the configurations with at least n(m - 1) grains injectively to those with at most (m - 1)(n - 1) grains, a disjoint set; hence twice the number of stochastically recurrent states is at most the number of stable configurations. For m = 2, direct all n sink edges into the second part, the edge from the non-sink first-part vertex a to b towards b when c(b) = 0 and towards a otherwise; then every configuration with at least n grains is recurrent, and the involution exchanges the configurations with at least n grains and those with at most n - 1, so equality holds. For m at least 3, the configuration with no grain on the first part and m - 2, m - 1, ..., m - 1 grains on the second part has n(m - 1) - 1 grains, which lies in neither set, so the inequality is strict.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alofi-2024-stochastic-sandpile-bipartite-half"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("ssmhalf-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Adj(Formula graph, Formula a, Formula b) => Call("Adj", graph, a, b);
    private static Formula NonSink(Formula v, Formula s) =>
        Seq(OpenBrace, v, Sp, Mid, Sp, Call("ne", v, s), CloseBrace);

    private static Formula OrientationFormula()
    {
        Formula g = F.Id("G"), o = F.Id("O"), u = F.Id("u"), v = F.Id("v"), vertices = F.Id("V");
        return Disp(Iff(Call("IsOrientation", g, o), All("u", vertices, All("v", vertices,
            Implies(Adj(g, u, v), Iff(Equal(new Formula.Apply(o, [u, v]), Named("true")),
                Equal(new Formula.Apply(o, [v, u]), Named("false"))))))));
    }

    private static Formula IndegFormula()
    {
        Formula g = F.Id("G"), o = F.Id("O"), u = F.Id("u"), v = F.Id("v");
        Formula into = Seq(OpenBrace, u, Sp, Mid, Sp,
            And(Adj(g, u, v), Equal(new Formula.Apply(o, [u, v]), Named("true"))), CloseBrace);
        return Disp(Equal(Call("indeg", g, o, v), Call("card", into)));
    }

    private static Formula StableFormula()
    {
        Formula g = F.Id("G"), s = F.Id("s"), v = F.Id("v");
        Formula domain = Seq(Open, v, Colon, Sp, NonSink(v, s), Close);
        return Disp(Equal(Call("Stable", g, s),
            new Formula.TypeArrow(domain, Call("Fin", Call("degree", g, v)))));
    }

    private static Formula StoFormula()
    {
        Formula g = F.Id("G"), s = F.Id("s"), c = F.Id("c"), o = F.Id("O"), v = F.Id("v");
        Formula compatible = All("v", NonSink(v, s),
            AtMost(Call("degree", g, v), Add(Call("indeg", g, o, v), new Formula.Apply(c, [v]))));
        Formula orientations = new Formula.TypeArrow(F.Id("V"), new Formula.TypeArrow(F.Id("V"), Named("Bool")));
        Formula recurrent = Ex("O", orientations, And(Call("IsOrientation", g, o), compatible));
        return Disp(Equal(Call("Sto", g, s),
            Seq(OpenBrace, c, Sp, InMacro, Sp, Call("Stable", g, s), Sp, Mid, Sp, recurrent, CloseBrace)));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula graph = Call("completeBipartiteGraph", Call("Fin", m), Call("Fin", n));
        Formula sto = Call("card", Call("Sto", graph, Call("inl", D(0))));
        Formula stable = Times(new Formula.Power(n, Subtract(m, D(1))), new Formula.Power(m, n));
        Formula bound = And(AtMost(Times(D(2), sto), stable),
            Parenthesized(Iff(Equal(Times(D(2), sto), stable), Equal(m, D(2)))));
        return Disp(Iff(F.Id("claim"), All("m", Naturals(), All("n", Naturals(),
            Implies(AtMost(D(2), m), Implies(AtMost(D(1), n), bound))))));
    }
}
