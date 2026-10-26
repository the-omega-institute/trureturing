using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

internal sealed class MazorchukXuClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Mazorchuk-Xu triangular family has a repeated-point closure rule equivalent to two universal rules on ordered edges.",
        H("Triangular subsets and ordered closure"),
        Blocks(
            Node("Closure", "triangle", "The source triangle", Triangle(),
                "Natural coordinates represent the nonnegative integer coordinates in Section 3, before Section 3.1. No nonempty-row condition is imposed.", DescribeRole.Definition, true),
            Node("Closure", "Star", "Repeated-point closure", StarFormula(),
                "The three selected points may coincide. Both forced points, including the conditional successor/minimum point, are retained.", DescribeRole.Definition, true),
            Node("Closure", "firstColumnCard", "First-column count", FirstColumn(),
                "Only points whose first coordinate is zero are counted.", DescribeRole.Definition, true),
            Node("Closure", "family", "The finite family R(n,k)", Family(),
                "All subsets of the triangle are tested. Empty subsets and empty rows remain in the domain.", DescribeRole.Definition, true),
            Node("Closure", "count", "The cardinal r(n,k)", Many("n k", N, Eq(Fn("count", V("n"), V("k")), Fn("card", Fn("family", V("n"), V("k"))))),
                "The first argument is a natural number. This definition introduces no recurrence value at minus one.", DescribeRole.Definition, true),
            Node("Closure", "Conjecture", "The complete polynomiality question", ConjectureFormula(),
                "For each deficit one rational polynomial must work at every valid natural rank, with exact degree and leading coefficient. Rational coefficients embed into real numerical values. This is the question's statement; no proof of this proposition is asserted here. Deficits zero through three are prior source results.", DescribeRole.Definition, true),
            Node("Closure", "pointEdges", "Point-to-edge relation", All("Y", Points, Many("a b", N,
                Iff(Fn("pointEdges", V("Y"), V("a"), V("b")), And(Lt(V("a"), V("b")), Mem(Pair(V("a"), Sub(V("b"), D(1))), V("Y")))))),
                "The source point (a,b) becomes the strict edge (a,b+1). Natural subtraction appears only after strict endpoint order has ensured a positive upper endpoint.", DescribeRole.Definition),
            Node("Closure", "Rules", "The rules P and J", RulesFormula(),
                "P propagates an overlapping pair to its upper-right edge. J joins the two lower endpoints and the two upper endpoints by maxima. Ordered edges are strict.", DescribeRole.Definition),
            Node("Closure", "mem_triangle", "Triangle membership", Many("n a b", N,
                Iff(Mem(Pair(V("a"), V("b")), Fn("triangle", V("n"))), And(Le(V("a"), V("b")), Le(V("b"), V("n"))))),
                "The finite range construction is exactly a less-than-or-equal b less-than-or-equal n.", DescribeRole.Theorem),
            Node("Closure", "star_iff_rules", "Literal source equivalence", All("Y", Points,
                Imp(OrderedPoints(V("Y")), Iff(Fn("Star", V("Y")), Fn("Rules", Fn("pointEdges", V("Y")))))),
                "Repeating the second source point gives P. J is the source's maximum conclusion. Conversely P, applied to the premise with the smaller upper endpoint, recovers the entire successor/minimum conclusion. This proves both directions for every triangular subset, including repetitions and empty subsets.", DescribeRole.Theorem),
            Node("Closure", "mem_family_iff", "Exact finite-family membership", Many("n k", N, All("Y", Points,
                Iff(Mem(V("Y"), Fn("family", V("n"), V("k"))), And(Subset(V("Y"), Fn("triangle", V("n"))), Fn("Rules", Fn("pointEdges", V("Y"))), Eq(Fn("firstColumnCard", V("Y")), V("k")))))),
                "The source-family test retains the triangle bound, both ordered-edge rules and the exact first-column statistic.", DescribeRole.Theorem)), []));

    private static Formula OrderedPoints(Formula y) => Many("a b", N,
        Imp(Mem(Pair(V("a"), V("b")), y), Le(V("a"), V("b"))));
    private static Formula Triangle() => All("n", N, Eq(Fn("triangle", V("n")),
        Set("p", Pairs, And(Le(Fn("fst", V("p")), Fn("snd", V("p"))), Le(Fn("snd", V("p")), V("n"))))));
    private static Formula FirstColumn() => All("Y", Points, Eq(Fn("firstColumnCard", V("Y")),
        Fn("card", Set("p", V("Y"), Eq(Fn("fst", V("p")), D(0))))));
    private static Formula Family() => Many("n k", N, Eq(Fn("family", V("n"), V("k")),
        Set("Y", Points, And(Subset(V("Y"), Fn("triangle", V("n"))), Fn("Star", V("Y")), Eq(Fn("firstColumnCard", V("Y")), V("k"))))));
    private static Formula StarFormula()
    {
        var a = V("a"); var b = V("b"); var c = V("c"); var d = V("d"); var e = V("e"); var f = V("f"); var y = V("Y");
        return All("Y", Points, Iff(Fn("Star", y), Many("a b c d e f", N,
            Imp(And(Mem(Pair(a,b),y),Mem(Pair(c,d),y),Mem(Pair(e,f),y),Le(a,c),Le(c,b),Le(a,e),Le(e,b),Le(b,d),Le(b,f)),
                And(Mem(Pair(Fn("max",c,e),Fn("max",d,f)),y),
                    Imp(Lt(b,Fn("min",d,f)),Mem(Pair(Plus(b,D(1)),Fn("min",d,f)),y)))))));
    }
    private static Formula ConjectureFormula()
    {
        var i=V("i");var p=V("p");var n=V("n");
        return Iff(Fn("Conjecture"),All("i",N,Ex("p",Fn("Polynomial",Q),And(
            Eq(Fn("natDegree",p),Mul(D(2),i)),Eq(Fn("leadingCoeff",p),Fn("inv",Fn("castRat",Fn("factorial",i)))),
            All("n",N,Imp(Le(i,Plus(n,D(1))),Eq(Fn("eval",p,Fn("castRat",n)),Fn("castRat",Fn("count",n,Sub(Plus(n,D(1)),i))))))))));
    }
    private static Formula RulesFormula()
    {
        var a=V("a");var b=V("b");var c=V("c");var d=V("d");var e=V("e");var f=V("f");var A=V("A");
        Formula E(Formula u,Formula v)=>Fn("E",u,v);
        var ordered=Many("a b",A,Imp(E(a,b),Lt(a,b)));
        var propagation=Many("a b c d",A,Imp(And(E(a,b),E(c,d),Le(a,c),Lt(c,b),Lt(b,d)),E(b,d)));
        var join=Many("a b c d e f",A,Imp(And(E(a,b),E(c,d),E(e,f),Le(a,c),Lt(c,b),Le(a,e),Lt(e,b),Le(b,d),Le(b,f)),E(Fn("max",c,e),Fn("max",d,f))));
        return Ordered("A",All("E",Rel(A),Iff(Fn("Rules",V("E")),And(ordered,propagation,join))));
    }
}
