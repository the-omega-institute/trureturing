using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorFrontierDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frontier refinement of the smooth fold", H("Frontier refinement of the smooth fold"),
        Blocks(
            Node("sum_refine", "Refinement preserves the smooth fold", Refine(),
                "For a node (p::ps,c), powList visits c p^e starting at exponent zero, " +
                "stopping at the first value above X or after 64 steps. The visited starts " +
                "give the child nodes (ps,c p^e), refined depth first. A node with no " +
                "generators is retained. Refinement also keeps a node that passes the " +
                "stopping test leaf or lies k levels below the root. Each expansion " +
                "splits smoothSum along the powers of the first generator, so for every " +
                "weight w, stopping test and depth the node sum of the refinement equals " +
                "the fold of the root."),
            Node("smoothSum_eq_of_frontierOk", "A checked frontier carries the root fold",
                Frontier(),
                "The test frontierOk X k (ps,c) F is true when the refinement of (ps,c) " +
                "to depth k, stopped at the nodes of F, returns exactly the list F. By " +
                "the refinement identity, for every weight w the root fold then equals " +
                "the mapped sum of smoothSum w ps X c over (ps,c) in F. " +
                "List.map_append and List.sum_append split concatenated frontiers directly."))));

    private static Formula MappedSum(Formula w, Formula x, Formula nodes) =>
        Call("sum", Call("mapSmoothSum", w, x, nodes));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose) => Describe.Lean(
        DescribeId.Create("smooth-predecessor-frontier-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Refine()
    {
        var w = V("w"); var x = V("X"); var leaf = V("leaf"); var k = V("k");
        var ps = V("ps"); var c = V("c");
        return B(Eq(MappedSum( w, x, Call("refine", x, leaf, k, Call("pair", ps, c))),
                Call("smoothSum", w, ps, x, c)),
            ("w", Arrow()), ("X", Nat()), ("leaf", Test()), ("k", Nat()),
            ("ps", List(Nat())), ("c", Nat()));
    }
    private static Formula Frontier()
    {
        var w = V("w"); var x = V("X"); var k = V("k"); var ps = V("ps"); var c = V("c");
        var f = V("F");
        return B(Imp(Eq(Call("frontierOk", x, k, Call("pair", ps, c), f), True()),
                Eq(Call("smoothSum", w, ps, x, c), MappedSum( w, x, f))),
            ("w", Arrow()), ("X", Nat()), ("k", Nat()), ("ps", List(Nat())), ("c", Nat()),
            ("F", Nodes()));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Arrow() => new Formula.TypeArrow(Nat(), Nat());
    private static Formula List(Formula a) => Call("List", a);
    private static Formula Nodes() => List(Call("Pair", List(Nat()), Nat()));
    private static Formula True() => V("true");
    private static Formula Test() =>
        new Formula.TypeArrow(Call("Pair", List(Nat()), Nat()), V("Bool"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula B(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = All(variables[i].Name, variables[i].Type, body);
        return body;
    }
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
