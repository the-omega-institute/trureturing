using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class TsiCoordinationSequenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/TsiCoordinationSequence";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/barker2018a299289");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating prism graph has coordination numbers (13n squared + 4)/2 at positive even radii "
            + "and (13n squared + 3)/2 at odd radii.",
        H("The coordination sequence of the alternating prism graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tsi-graph"),
                DeclarationHandle.Create(Module + ".tsiGraph"),
                H("Square layers with alternating prism slabs"),
                StatementSource.FromAuthor(Disp(GraphFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vertices are integer triples, with the third coordinate specifying the layer. "
                        + "Within each layer, adjacent vertices differ by one in exactly one horizontal coordinate. "
                        + "From layer k to layer k+1, each vertex is joined to the vertex with the same horizontal "
                        + "coordinates and to one shifted by one in the first coordinate when k is even, "
                        + "or in the second coordinate when k is odd. The last two alternatives include both "
                        + "directions of these interlayer edges. This is the combinatorial alternating prism model "
                        + "of the tsi net; its geometric realization as a tiling is not part of the statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shell"),
                DeclarationHandle.Create(Module + ".shell"),
                H("The coordination number at a radius"),
                StatementSource.FromAuthor(Disp(ShellFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural radius n, shell n counts the vertices at graph distance exactly n "
                        + "from the origin. Set.ncard is natural-valued; the distance formula below shows that "
                        + "each such sphere is finite. The center is the specified vertex (0,0,0)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The two conjectural closed forms"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The source labels the two formulas as conjectures. For the graph and center specified here, "
                        + "the proposition asserts the even formula at every positive even natural radius "
                        + "and the odd formula at every odd natural radius. Multiplication by two expresses "
                        + "both formulas as equalities of natural numbers. The generating function, recurrence "
                        + "and partial sums are not additional conjuncts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The coordination formulas hold at every positive radius"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First measure the distance of an integer i from the integer interval with endpoints "
                            + "0 and c as the natural number Int.toNat(min(0, c) − i) + Int.toNat(i − max(0, c)); "
                            + "Int.toNat sends a negative integer to zero.")),
                    Paragraph(Text(
                        "For an integer triple (i,j,k), add the layer displacement Int.natAbs k, the distance "
                            + "of i from the interval with endpoints 0 and (k+1)/2, and the distance of j from "
                            + "the interval with endpoints 0 and k/2. These divisions are integer divisions, "
                            + "which round down for the divisor 2.")),
                    Paragraph(Text(
                        "A horizontal edge changes this expression by at most one. To check an interlayer edge, "
                            + "split the absolute layer coordinate into the sum of the absolute values of "
                            + "(k+1)/2 and k/2. For even k only the first interval endpoint increases, and "
                            + "for odd k only the second increases. In either case, a shift by zero or one "
                            + "in that coordinate changes the corresponding absolute-value-plus-interval-distance "
                            + "term by at most one. Thus the expression changes by at most one along every edge.")),
                    Paragraph(Text(
                        "Every vertex with a positive value has an adjacent vertex whose value is one smaller. "
                            + "If a horizontal coordinate is outside its interval, move it one unit toward that "
                            + "interval. Otherwise both coordinates are inside their intervals. Move the layer "
                            + "one step toward zero, adjusting the first or second coordinate at an endpoint "
                            + "as required by the parity and sign of k. The new coordinates remain in the smaller "
                            + "rectangle. Value zero forces all three coordinates to be zero. Strong induction "
                            + "therefore constructs a walk from the origin with length equal to the expression. "
                            + "This gives the upper bound on distance. Applying the edge estimate to the reverse "
                            + "reachable pair, with value zero at the origin, gives the lower bound. Hence, with "
                            + "integer division rounding down in the interval endpoints:")),
                    new DocumentBlock.DisplayFormula(MetricFormula()),
                    Paragraph(Text(
                        "Next count the one-dimensional shells. At interval distance zero there are "
                            + "Int.natAbs c + 1 integers; at each positive interval distance there are exactly "
                            + "two, one beyond each endpoint. For a rectangle with interval endpoints (0,c) "
                            + "and (0,e), split a prescribed total distance d into t and d−t for t from zero "
                            + "through d. The resulting Cartesian products are disjoint because their first "
                            + "interval distances differ. Multiplying the interval counts gives "
                            + "(Int.natAbs c + 1)(Int.natAbs e + 1) at d=0. For d>0 the two end terms "
                            + "and the d−1 interior terms sum to 2(Int.natAbs c + Int.natAbs e) + 4d.")),
                    Paragraph(Text(
                        "The sphere of radius n is the disjoint union of these rectangle shells over the "
                            + "integer layers from −n to n. In layer k the endpoints are (k+1)/2 and k/2, "
                            + "and the residual distance is n−Int.natAbs k. Embedding each horizontal pair "
                            + "as (i,j,k) is injective, and distinct layers are disjoint, so their finite "
                            + "cardinalities add to shell n.")),
                    Paragraph(Text(
                        "For positive n, each of the two extreme layers has "
                            + "(n/2+1)((n+1)/2+1) vertices. In an interior layer the sum of the two "
                            + "absolute interval endpoints is Int.natAbs k, so the rectangle count simplifies "
                            + "to 4n−2 Int.natAbs k. Cast the layer counts to integers and use symmetry in k "
                            + "to sum over the nonnegative layers. The sum of the integers from zero through "
                            + "n−1 is evaluated by twice that sum being n(n−1). Converting the resulting "
                            + "equality back to natural numbers gives the following identity, in which the "
                            + "divisions on natural numbers are floor divisions, exactly Lean's Nat.div:")),
                    new DocumentBlock.DisplayFormula(SumFormula()),
                    Paragraph(Text(
                        "Finally, if n is positive and even, write n=t+t. Both n/2 and (n+1)/2 equal t; "
                            + "substitution into the sum identity yields 2 shell n = 13 n² + 4. "
                            + "If n is odd, write n=t+t+1. Then n is positive, n/2=t and (n+1)/2=t+1; "
                            + "the same identity yields 2 shell n = 13 n² + 3. These two arguments prove "
                            + "the two conjuncts."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barker-2018-oeis-a299289-tsi-coordination-sequence"),
                    ResolutionKind.Proved)))));

    private static Formula GraphFormula()
    {
        var u = X("u");
        var v = X("v");
        var ux = Coordinate(u, 1);
        var uy = Coordinate(u, 2);
        var uz = Coordinate(u, 3);
        var vx = Coordinate(v, 1);
        var vy = Coordinate(v, 2);
        var vz = Coordinate(v, 3);
        var horizontalX = And(Equal(uz, vz), And(Equal(uy, vy),
            Or(Equal(ux, Add(vx, D(1))), Equal(vx, Add(ux, D(1))))));
        var horizontalY = And(Equal(uz, vz), And(Equal(ux, vx),
            Or(Equal(uy, Add(vy, D(1))), Equal(vy, Add(uy, D(1))))));
        return All("u", Vertices(), All("v", Vertices(),
            Equivalence(At(Qualified("SimpleGraph", "Adj"), Local("tsiGraph"), u, v),
                Or(horizontalX, Or(horizontalY, Or(
                    And(Equal(vz, Add(uz, D(1))), Slab(ux, uy, uz, vx, vy)),
                    And(Equal(uz, Add(vz, D(1))), Slab(vx, vy, vz, ux, uy))))))));
    }

    private static Formula Slab(Formula i, Formula j, Formula k, Formula a, Formula b) =>
        Or(And(Equal(a, i), Equal(b, j)),
            Or(And(At(Qualified("Even"), k), And(Equal(a, Add(i, D(1))), Equal(b, j))),
                And(At(Qualified("Odd"), k), And(Equal(a, i), Equal(b, Add(j, D(1)))))));

    private static Formula ShellFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("shell", X("n")), Naturals()),
            At(Qualified("Set", "ncard"), Seq(OpenBrace, X("v"), Colon, Sp, Vertices(), Sp, Mid, Sp,
                Equal(Distance(X("v")), X("n")), CloseBrace))));

    private static Formula ClaimFormula() => And(
        All("n", Naturals(), Arrow(Less(D(0), X("n")),
            Arrow(At(Qualified("Even"), X("n")), ClosedForm(D(4))))),
        All("n", Naturals(), Arrow(At(Qualified("Odd"), X("n")), ClosedForm(D(3)))));

    private static Formula ClosedForm(Formula constant) =>
        Equal(Multiply(D(2), LocalCall("shell", X("n"))),
            Add(Multiply(D(1, 3), new Formula.Power(X("n"), D(2))), constant));

    private static Formula MetricFormula() => IntegerTripleBinders(
        Equal(Distance(Triple(X("i"), X("j"), X("k"))), RadiusFormulaExpression()));

    private static Formula SumFormula() => All("n", Naturals(), Arrow(Less(D(0), X("n")),
        Equal(Add(LocalCall("shell", X("n")), Multiply(D(2), X("n"))),
            Add(Multiply(D(6), new Formula.Power(X("n"), D(2))),
                Multiply(D(2), Multiply(Add(NaturalDivide(X("n"), D(2)), D(1)),
                    Add(NaturalDivide(Add(X("n"), D(1)), D(2)), D(1))))))));

    private static Formula IntegerTripleBinders(Formula body) =>
        All("i", Integers(), All("j", Integers(), All("k", Integers(), body)));
    private static Formula GapFormula(Formula c, Formula i) =>
        Add(At(Qualified("Int", "toNat"), Subtract(At(Qualified("min"), D(0), c), i)),
            At(Qualified("Int", "toNat"), Subtract(i, At(Qualified("max"), D(0), c))));
    private static Formula RadiusFormulaExpression() =>
        Add(Add(At(Qualified("Int", "natAbs"), X("k")),
                GapFormula(IntegerDivide(Add(X("k"), D(1)), D(2)), X("i"))),
            GapFormula(IntegerDivide(X("k"), D(2)), X("j")));
    private static Formula Distance(Formula v) => At(Qualified("SimpleGraph", "dist"),
        Local("tsiGraph"), Typed(Triple(D(0), D(0), D(0)), Vertices()), v);
    private static Formula Coordinate(Formula v, int coordinate) => coordinate switch
    {
        1 => Seq(v, Dot, D(1)),
        2 => Seq(v, Dot, D(2), Dot, D(1)),
        _ => Seq(v, Dot, D(2), Dot, D(2)),
    };
    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Parenthesized(Seq(a, Comma, Sp, b, Comma, Sp, c));
    private static Formula Vertices() => Seq(Integers(), Sp, Times, Sp,
        Parenthesized(Seq(Integers(), Sp, Times, Sp, Integers())));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics", "TsiCoordinationSequence", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula IntegerDivide(Formula left, Formula right) =>
        At(Qualified("HDiv", "hDiv"), Typed(left, Integers()), Typed(right, Integers()));
    private static Formula NaturalDivide(Formula left, Formula right) =>
        At(Qualified("HDiv", "hDiv"), Typed(left, Naturals()), Typed(right, Naturals()));
}
