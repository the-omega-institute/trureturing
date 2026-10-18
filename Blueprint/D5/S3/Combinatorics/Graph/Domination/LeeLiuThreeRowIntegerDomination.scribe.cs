using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class LeeLiuThreeRowIntegerDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/leeliu2025integerdomination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer {2}-domination number of the three-row Cartesian grid is ⌊3n/2⌋ + 1 for every positive n. A potential on pairs of three-entry columns gives the lower bound, and alternating columns attain it.",
        H("Integer {2}-domination of three-row grids"),
        Blocks(
            Node("grid", "The Cartesian grid", GridFormula(),
                "Lee and Liu, Section 1 (p. 2): \"For positive integers m and n, the grid graph Gm,n = Pm □ Pn is the Cartesian product of path graphs Pm and Pn.\" The pair (i,j) in Fin m × Fin n represents the vertex v at row i+1 and column j+1. The operation □ is SimpleGraph.boxProd, and SimpleGraph.pathGraph joins consecutive indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsTwoDominating", "Integer {2}-dominating functions", DominatingFormula(),
                "Lee and Liu, Abstract (p. 1): \"An integer {2}-dominating function of a graph is a mapping from the vertex set to {0, 1, 2} such that the sum of the mapped values of each vertex and its neighbors is at least 2; the integer {2}-domination number of a graph is defined to be the minimum sum of mapped values of all vertices among all integer {2}-dominating functions.\" A natural-number value bounded by 2 is in {0,1,2}. The sum uses the open neighbour set and adds f(v) once, giving precisely the closed-neighbourhood sum. Section 1 allows all nonnegative integer values; truncation at 2 preserves feasibility and cannot increase weight.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gamma2", "The minimum weight", GammaFormula(),
                "Lee and Liu, Abstract (p. 1): \"An integer {2}-dominating function of a graph is a mapping from the vertex set to {0, 1, 2} such that the sum of the mapped values of each vertex and its neighbors is at least 2; the integer {2}-domination number of a graph is defined to be the minimum sum of mapped values of all vertices among all integer {2}-dominating functions.\" The natural-number infimum is taken over attained weights. The constant function 2 makes this set nonempty; hence its infimum is its minimum. Every labelled vertex contributes once to the sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Lee–Liu Conjecture 2.5", Disp(Iff(X("claim"), ClaimBody())),
                "Lee and Liu, Conjecture 2.5 (p. 11): \"For positive integer n, we have γ{2}(G3,n) = ⌊3n/2⌋ + 1.\" The row count is 3, the column count ranges over all natural numbers at least 1, and division is natural-number division, written Nat.div. Thus Nat.div (3*n) 2 equals ⌊3n/2⌋.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The exact value for every positive width", Disp(ClaimBody()),
                "A column is encoded by a number in Fin 27. For columns a,b,c the domination condition depends only on those three columns. An integer table R on pairs of columns defines Φ(a,b) = 2s(a)+2s(b)+R(a,b), where s is the column weight. Its initial inequality is Φ(0,b) ≤ 2s(b)−3; every admissible step satisfies Φ(b,c) ≤ Φ(a,b)+2s(c)−3; every terminal pair satisfies 1 ≤ Φ(a,b). Summing gives 1 ≤ 2W−3n, so W ≥ ⌊3n/2⌋+1. The construction of Theorem 2.4 puts (1,1,1) in even columns and (0,1,0) in column 1 and in the last column when n is odd; other columns are zero. For n=1 use (0,2,0). Its weight is exactly ⌊3n/2⌋+1. Together these bounds prove the displayed equality for every n ≥ 1, including the values computed in Remark 2.6.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-liu-2025-integer-two-domination-three-row"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ll-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. arguments]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula value, params Formula[] arguments) =>
        new Formula.Apply(value, [.. arguments]);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula m, Formula n) =>
        Seq(Fin(m), Sp, Times, Sp, Fin(n));
    private static Formula Maps(Formula m, Formula n) =>
        Seq(Parenthesized(Vertices(m, n)), Sp, To, Sp, Nat);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Eq(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Path(Formula n) => App(Q("SimpleGraph", "pathGraph"), n);
    private static Formula Neighbours(Formula graph, Formula vertex) =>
        App(Q("SimpleGraph", "neighborFinset"), graph, vertex);
    private static Formula Sum(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(X(variable), Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula SumAll(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(X(variable), Sp, Colon, Sp, type)), Sp, body);

    private static Formula GridFormula()
    {
        Formula m = X("m"), n = X("n");
        return Disp(All("m", Nat, All("n", Nat,
            Eq(Call("grid", m, n), App(Q("SimpleGraph", "boxProd"), Path(m), Path(n))))));
    }

    private static Formula DominatingFormula()
    {
        Formula m = X("m"), n = X("n"), f = X("f"), v = X("v"), u = X("u");
        return Disp(All("m", Nat, All("n", Nat, All("f", Maps(m, n),
            Iff(Call("IsTwoDominating", m, n, f),
                And(All("v", Vertices(m, n), Le(App(f, v), D(2))),
                    All("v", Vertices(m, n), Le(D(2), Add(App(f, v),
                        Sum("u", Neighbours(Call("grid", m, n), v), App(f, u)))))))))));
    }

    private static Formula GammaFormula()
    {
        Formula m = X("m"), n = X("n"), f = X("f"), w = X("w");
        Formula weights = Seq(OpenBrace, w, Sp, Colon, Sp, Nat, Sp, Mid, Sp,
            ExistsIn("f", Maps(m, n), And(Call("IsTwoDominating", m, n, f),
                Eq(SumAll("v", Vertices(m, n), App(f, X("v"))), w))), CloseBrace);
        return Disp(All("m", Nat, All("n", Nat,
            Eq(Call("gamma2", m, n), Call("sInf", weights)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n");
        Formula threeN = new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, n);
        return All("n", Nat, Implies(Le(D(1), n),
            Eq(Call("gamma2", D(3), n), Add(App(Q("Nat", "div"), threeN, D(2)), D(1)))));
    }

}
