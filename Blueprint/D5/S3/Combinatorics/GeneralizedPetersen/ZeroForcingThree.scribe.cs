using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var type = V("V"); var g = V("G"); var s = V("S"); var t = V("T");
        var v = V("v"); var u = V("u"); var w = V("w"); var x = V("x");
        var b = V("B"); var f = V("F"); var e = V("e"); var n = V("n");
        var k = V("k"); var p = V("p"); var selected = V("X");
        var setType = Call("Set", type);
        var closure = And(SubsetOf(s, b), Q(Imp(And(Mem(u, b), Adj(g, u, w),
            Q(Imp(And(Adj(g, u, x), Ne(x, w)), Mem(x, b)), ("x", type))),
            Mem(w, b)), ("u", type), ("w", type)));
        var graphVariables = new (string Name, Formula Domain)[]
            { ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("S", setType) };
        return DocumentDefinition.Create(ScribeNode.Create(
            "Eight vertices are necessary and sufficient to zero-force P(n,3) for every n at least thirteen.",
            H("The Zero Forcing Number of P(n,3)"),
            Blocks(
            Node("black", "Closure under the color-change rule", "Black",
                Disp(Q(Iff(Call("Black", g, s, v), Q(Imp(closure, Mem(v, b)), ("B", setType))), [.. graphVariables, ("v", type)])),
                "Black is the least set containing the initially black vertices S and closed under the color-change rule. A black source forces a neighboring vertex whenever all its other neighbors are black.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zero-forcing", "A zero forcing set", "IsZeroForcing",
                Disp(Q(Iff(Call("IsZeroForcing", g, s), Q(Call("Black", g, s, v), ("v", type))), graphVariables)),
                "A set is zero forcing when its closure contains every vertex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zero-forcing-number", "The minimum number of initial vertices", "zeroForcingNumber",
                Disp(Q(Eq(Call("zeroForcingNumber", g), Call("sInf", SetOf("k", Nat(), Ex("S", Fs(type), And(Eq(Card(s), k), Call("IsZeroForcing", g, s)))))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)))),
                "The zero forcing number is the infimum in the natural numbers of the cardinalities of finite zero forcing sets.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Krishnan Conjecture 5", "claim",
                Disp(Iff(Name("claim"), Q(Imp(Le(Num(13), n), Eq(Call("zeroForcingNumber", Call("gp", n, Num(3))), Num(8))), ("n", Nat())))),
                "Conjecture 5 asserts that the zero forcing number of P(n,3) is eight for every natural n at least thirteen.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("black-monotone", "Enlarging the initial black set", "mono",
                Disp(Q(Imp(And(SubsetOf(s, t), Call("Black", g, s, v)), Call("Black", g, t, v)), [.. graphVariables, ("T", setType), ("v", type)])),
                "Every forcing derivation from S remains valid after the initial set is enlarged to T.",
                DescribeRole.Theorem),
            Node("initial-force", "A first force inside a derivation", "exists_initial_force",
                Disp(Q(Imp(And(Call("Black", g, s, v), Not(Mem(v, s))), Ex("u", type, Ex("w", type, And(Mem(u, s), Not(Mem(w, s)), Adj(g, u, w), Q(Imp(And(Adj(g, u, x), Ne(x, w)), Mem(x, s)), ("x", type)))))), [.. graphVariables, ("v", type)])),
                "A derivation reaching a vertex outside S contains an oriented edge whose source and all other neighbors are already in S, while its target is outside S.",
                DescribeRole.Theorem),
            Node("transport", "Transporting black vertices by an automorphism", "image_equiv",
                Disp(Q(Imp(And(Q(Iff(Adj(g, Call("e", x), Call("e", V("y"))), Adj(g, x, V("y"))), ("x", type), ("y", type)), Call("Black", g, s, v)), Call("Black", g, Image(s, "x", Call("e", x)), Call("e", v))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("e", Seq(type, Equiv, Sp, type)), ("S", Fs(type)), ("v", type))),
                "An adjacency-preserving equivalence carries every forcing step to a forcing step from the image of the initial finite set.",
                DescribeRole.Theorem),
            Node("fort-obstruction", "A disjoint fort remains white", "not_black_of_disjoint",
                Disp(Q(Imp(And(Call("Finite", type), Call("IsFort", g, f), Call("Disjoint", s, f), Mem(v, f)), Not(Call("Black", g, s, v))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("S", Fs(type)), ("F", Fs(type)), ("v", type))),
                "If the initial set is disjoint from a fort, no vertex of the fort can become black.",
                DescribeRole.Theorem),
            Node("substitution", "Substituting forcing derivations", "bind",
                Disp(Q(Imp(And(Q(Imp(Mem(x, t), Call("Black", g, s, x)), ("x", type)), Call("Black", g, t, v)), Call("Black", g, s, v)), [.. graphVariables, ("T", setType), ("v", type)])),
                "If every vertex of T can be forced from S, every vertex forced from T can also be forced from S.",
                DescribeRole.Theorem),
            Node("eight-outer", "Eight consecutive outer vertices suffice", "outerBlock8_zeroForcing",
                Disp(Q(Imp(Le(Num(9), n), Call("IsZeroForcing", Call("gp", n, Num(3)), Image(Call("range", Num(8)), "i", Pair(False(), Call("ofNat", n, V("i")))))), ("n", Nat()))),
                "For n at least nine, the outer vertices at columns zero through seven force all inner and outer vertices. The proof first forces inner vertices and extends the outer block, then propagates around the cycle.",
                DescribeRole.Theorem),
            Node("external-boundary", "External boundary of a finite graph", "externalBoundary",
                Disp(Q(Imp(Call("Finite", type), Eq(Call("externalBoundary", g, selected), SetOf("v", type, And(Not(Mem(v, selected)), Ex("u", type, And(Mem(u, selected), Adj(g, u, v))))))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("X", Fs(type)))),
                "The external boundary consists of vertices outside the selected set with at least one neighbor in it.",
                DescribeRole.Definition),
            Node("first-forcers", "The boundary of the first forcing sources", "firstForcers_boundary",
                Disp(Q(Imp(And(Call("Finite", type), Call("IsZeroForcing", g, s), Le(Add(Card(s), p), Card(type))), Ex("X", Fs(type), And(Eq(Card(selected), p), Le(Card(Call("externalBoundary", g, selected)), Card(s))))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("S", Fs(type)), ("p", Nat()))),
                "If at least p forces are possible, there is a set of p distinct forcing sources whose external boundary has size at most the initial set.",
                DescribeRole.Theorem),
            Node("thirteen", "The thirteen-column case", "zeroForcingNumber13",
                Disp(Eq(Call("zeroForcingNumber", Call("gp", Num(13), Num(3))), Num(8))),
                "The eight-vertex construction gives the upper bound. Every seven-vertex candidate with an initial force rotates into one of six anchor families, each containing a disjoint fort, which gives the lower bound.",
                DescribeRole.Theorem),
            Node("result", "Eight for every circumference at least thirteen", "result",
                Disp(Q(Imp(Le(Num(13), n), Eq(Call("zeroForcingNumber", Call("gp", n, Num(3))), Num(8))), ("n", Nat()))),
                "For n at least fourteen, every ten-vertex set has external boundary at least eight. Applying the first-forcers inequality with ten sources excludes initial sets of at most seven vertices. The thirteen-column fort argument and the uniform eight-vertex construction complete the equality.",
                DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(ProblemSlugRef.Create("krishnan-zero-forcing-generalized-petersen-three"), ResolutionKind.Proved))),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula SetOf(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, V(variable), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula False() => Name("false");
    private static Formula Adj(Formula graph, Formula left, Formula right) => Call("Adj", graph, left, right);
}
