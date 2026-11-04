using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class TeaCoordinationSequenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/TeaCoordinationSequence";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/barker2018a299285");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tea slab graph has eight times its coordination number equal to 63n squared "
            + "plus 16, 17, 12 or 17 according to the positive radius modulo four.",
        H("The coordination sequence of the tea slab graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tea-graph"),
                DeclarationHandle.Create(Module + ".teaGraph"),
                H("Triangular layers with alternating tetrahedral and prism slabs"),
                StatementSource.FromAuthor(Disp(GraphFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Vertices are integer triples, with the third coordinate specifying the layer. "
                        + "Each layer is a triangular lattice: its six edge differences in the first two "
                        + "coordinates are (1,0), (−1,0), (0,1), (0,−1), (1,−1) and (−1,1). "
                        + "Between layers k and k+1 there is always an edge with unchanged horizontal coordinates. "
                        + "When k has remainder zero modulo four, there are also edges with horizontal shift "
                        + "(1,0) or (0,1); when its remainder is two, the additional shifts are (−1,0) "
                        + "or (0,−1). Odd layers have only the unchanged shift. The last two alternatives "
                        + "in the formula give both directions of the interlayer edges. This is the integer "
                        + "slab model of the tea net associated with OEIS A299285; the geometric identification "
                        + "with a tiling of three-dimensional space is outside the statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shell"),
                DeclarationHandle.Create(Module + ".shell"),
                H("The coordination number at a radius"),
                StatementSource.FromAuthor(Disp(ShellFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural radius n, shell n is the natural cardinality of the vertices "
                        + "at graph distance exactly n from (0,0,0). Set.ncard is natural-valued, "
                        + "and the distance and layer counts below show that each sphere is finite. "
                        + "The center is this specified origin."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The four conjectural coordination formulas"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The OEIS entry marks Barker's generating function and recurrence as conjectural "
                        + "and gives Spezia's closed form conditionally on them. Here that closed form is "
                        + "the proposition for the specified graph and origin: at every positive natural "
                        + "radius, eight times the coordination number is 63 times the squared radius "
                        + "plus the constant selected by its remainder modulo four. All four equalities "
                        + "are in the natural numbers. The generating function, recurrence and partial "
                        + "sums are not additional conjuncts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The coordination formulas hold at every positive radius"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a layer k, count separately the two orientations of tetrahedral slabs "
                            + "crossed from layer zero. For nonnegative k these counts are (k+3)/4 "
                            + "and (k+1)/4; for negative k they are (−k+2)/4 and (−k)/4. "
                            + "They are nonnegative integers. All divisions of integers here and in "
                            + "the distance formula are Lean's floor division Int.ediv. "
                            + "For nonnegative integer counts p and q, measure the horizontal excess "
                            + "by the maximum of zero and the six violations of the bounds "
                            + "−q ≤ i,j,i+j ≤ p. Being at most d is exactly the conjunction of "
                            + "d being nonnegative and the six bounds with endpoints −q−d and p+d.")),
                    Paragraph(Text(
                        "Add the absolute layer coordinate to the natural conversion of this maximum. "
                            + "Along a planar edge the maximum changes by at most one. For an interlayer "
                            + "edge, split according to the sign of the layer and its remainder modulo four. "
                            + "The slab counts and the permitted horizontal shifts make the whole "
                            + "natural-valued expression change by at most one.")),
                    Paragraph(Text(
                        "When the maximum is positive, a planar step decreases it by exactly one: "
                            + "split according to the signs of i and j and move toward the hexagonal region. "
                            + "When it is zero and the layer is nonzero, move one layer toward zero. "
                            + "Removing a slab of the first orientation either leaves the horizontal "
                            + "coordinates unchanged or subtracts one from one coordinate; removing the "
                            + "other orientation either leaves them unchanged or adds one to one coordinate. "
                            + "The six bounds ensure that one permitted choice lies in the smaller region. "
                            + "A prism step leaves the coordinates unchanged. These steps decrease the "
                            + "whole expression by exactly one. Value zero forces all three coordinates "
                            + "to be zero. Strong induction constructs a walk from the origin of exactly "
                            + "that length, proving the upper distance bound. Apply the edge estimate "
                            + "along a walk in the reverse direction, using value zero at the origin, "
                            + "to obtain the lower bound. Thus the exact distance is:")),
                    new DocumentBlock.DisplayFormula(MetricFormula()),
                    Paragraph(Text(
                        "Next fix nonnegative integer counts p and q. The zero-excess region consists "
                            + "of the integer pairs with all three of i, j and i+j between −q and p. "
                            + "Count its points by vertical slices. For each first coordinate i from "
                            + "−q through p, the second coordinate ranges from max(−q,−q−i) to "
                            + "min(p,p−i). Split the first coordinate into −q through −1 and zero "
                            + "through p; the slice lengths are p+q+1+i and p+q+1−i respectively. "
                            + "The half-open interval sum identity for complex casts gives, after "
                            + "casting back to integers, twice the sum of an integer interval as the "
                            + "sum of its endpoints times its cardinality. Summing the slice lengths "
                            + "therefore gives the following count. Nat.cast explicitly includes "
                            + "the natural cardinality in the integers:")),
                    new DocumentBlock.DisplayFormula(HexagonCountFormula()),
                    Paragraph(Text(
                        "At excess d greater than zero, the pairs form the difference of two "
                            + "nested hexagonal regions: the outer endpoints are −q−d and p+d, "
                            + "and the inner endpoints are −q−d+1 and p+d−1. Subtracting their "
                            + "cardinalities gives 3(p+q)+6d, as an integer count. At excess zero "
                            + "use the hexagonal count just established.")),
                    Paragraph(Text(
                        "For radius n, use the exact distance to partition the sphere into the "
                            + "integer layers from −n through n. In layer k the excess is the natural "
                            + "difference n−Int.natAbs k, and the two slab counts are those specified "
                            + "above. The finite horizontal regions embed injectively as (i,j,k); "
                            + "different layers are disjoint. A bijection with their dependent union "
                            + "therefore expresses shell n as the sum of their finite cardinalities.")),
                    Paragraph(Text(
                        "Assume n is positive and cast the layer counts to integers. Pair each "
                            + "nonnegative layer m with layer −m. The four slab counts in such a pair "
                            + "sum to m. For m less than n the positive-excess count consequently "
                            + "makes the paired contribution 12n−9m; at m=0 this counts the middle "
                            + "layer twice, whose contribution is 6n. At the two extreme layers "
                            + "the excess is zero. Twice their combined count is the sum, over those "
                            + "two layers, of the squares of the two slab counts plus four times "
                            + "their product, together with 3n+4. Pairing the full layer sum, "
                            + "subtracting the extra middle contribution and using twice the sum "
                            + "of zero through n−1 equal to n(n−1) shows that eight times shell n "
                            + "is 60n²+16 plus four times that sum of quadratic slab-count terms.")),
                    Paragraph(Text(
                        "Finally split n into its four remainders modulo four and use the integer "
                            + "quotient n/4, again with floor division Int.ediv. At remainder zero all "
                            + "four extreme-layer slab counts equal the quotient. At remainder one "
                            + "only the first count in layer n is one larger. At remainder two the "
                            + "first count in each extreme layer is one larger. At remainder three "
                            + "both counts in layer n and the first count in layer −n are one larger. "
                            + "Substitution into the quadratic expression gives the constants "
                            + "16, 17, 12 and 17 respectively after collecting 63n². Casting the "
                            + "equalities back to natural numbers proves the four implications. "
                            + "Replacing the layer sum by shell n proves their conjunction for "
                            + "every positive n."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barker-2018-oeis-a299285-tea-coordination-sequence"),
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
        var planar = Or(And(Equal(vx, Add(ux, D(1))), Equal(vy, uy)),
            Or(And(Equal(ux, Add(vx, D(1))), Equal(uy, vy)),
                Or(And(Equal(vx, ux), Equal(vy, Add(uy, D(1)))),
                    Or(And(Equal(ux, vx), Equal(uy, Add(vy, D(1)))),
                        Or(And(Equal(vx, Add(ux, D(1))), Equal(uy, Add(vy, D(1)))),
                            And(Equal(ux, Add(vx, D(1))), Equal(vy, Add(uy, D(1)))))))));
        return All("u", Vertices(), All("v", Vertices(),
            Equivalence(At(Qualified("SimpleGraph", "Adj"), Local("teaGraph"), u, v),
                Or(And(Equal(uz, vz), planar),
                    Or(And(Equal(vz, Add(uz, D(1))), Slab(ux, uy, uz, vx, vy)),
                        And(Equal(uz, Add(vz, D(1))), Slab(vx, vy, vz, ux, uy)))))));
    }

    private static Formula Slab(Formula i, Formula j, Formula k, Formula a, Formula b) =>
        Or(And(Equal(a, i), Equal(b, j)),
            Or(And(Equal(At(Qualified("Int", "emod"), k, D(4)), D(0)),
                    Or(And(Equal(a, Add(i, D(1))), Equal(b, j)),
                        And(Equal(a, i), Equal(b, Add(j, D(1)))))),
                And(Equal(At(Qualified("Int", "emod"), k, D(4)), D(2)),
                    Or(And(Equal(a, Subtract(i, D(1))), Equal(b, j)),
                        And(Equal(a, i), Equal(b, Subtract(j, D(1))))))));

    private static Formula ShellFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("shell", X("n")), Naturals()),
            At(Qualified("Set", "ncard"), Seq(OpenBrace, X("v"), Colon, Sp, Vertices(), Sp, Mid, Sp,
                Equal(Distance(X("v")), X("n")), CloseBrace))));

    private static Formula ClaimFormula() => All("n", Naturals(), Arrow(Less(D(0), X("n")),
        And(ResidueCase(D(0), D(1, 6)), And(ResidueCase(D(1), D(1, 7)),
            And(ResidueCase(D(2), D(1, 2)), ResidueCase(D(3), D(1, 7)))))));

    private static Formula ResidueCase(Formula residue, Formula constant) =>
        Arrow(Equal(At(Qualified("Nat", "mod"), X("n"), D(4)), residue),
            Equal(Multiply(D(8), LocalCall("shell", X("n"))),
                Add(Multiply(D(6, 3), new Formula.Power(X("n"), D(2))), constant)));

    private static Formula MetricFormula() =>
        All("i", Integers(), All("j", Integers(), All("k", Integers(),
            Equal(Distance(Triple(X("i"), X("j"), X("k"))),
                Add(At(Qualified("Int", "natAbs"), X("k")),
                    At(Qualified("Int", "toNat"), Excess(X("i"), X("j"),
                        FirstSlabCount(X("k")), SecondSlabCount(X("k")))))))));

    private static Formula FirstSlabCount(Formula k) =>
        At(Qualified("ite"), LessEqual(D(0), k),
            IntegerDivide(Add(k, D(3)), D(4)),
            IntegerDivide(Add(new Formula.Negate(k), D(2)), D(4)));

    private static Formula SecondSlabCount(Formula k) =>
        At(Qualified("ite"), LessEqual(D(0), k),
            IntegerDivide(Add(k, D(1)), D(4)), IntegerDivide(new Formula.Negate(k), D(4)));

    private static Formula Excess(Formula i, Formula j, Formula p, Formula q) =>
        At(Qualified("max"), D(0), At(Qualified("max"), Subtract(i, p),
            At(Qualified("max"), Subtract(j, p), At(Qualified("max"), Subtract(Add(i, j), p),
                At(Qualified("max"), Subtract(new Formula.Negate(q), i),
                    At(Qualified("max"), Subtract(new Formula.Negate(q), j),
                        Subtract(Subtract(new Formula.Negate(q), i), j)))))));

    private static Formula HexagonCountFormula()
    {
        var p = X("p");
        var q = X("q");
        var z = X("z");
        var total = Add(Coordinate(z, 1), Seq(z, Dot, D(2)));
        var predicate = Seq(Parenthesized(Seq(z, Colon, Sp, Pairs())), Sp, Mapsto, Sp,
            Parenthesized(And(LessEqual(new Formula.Negate(q), total), LessEqual(total, p))));
        var region = At(Qualified("Finset", "filter"), Parenthesized(predicate),
            At(Qualified("Finset", "product"),
                At(Qualified("Finset", "Icc"), new Formula.Negate(q), p),
                At(Qualified("Finset", "Icc"), new Formula.Negate(q), p)));
        var count = Typed(At(Qualified("Nat", "cast"), At(Qualified("Finset", "card"), region)), Integers());
        var polynomial = Add(Add(Add(Add(Add(new Formula.Power(p, D(2)),
            Multiply(Multiply(D(4), p), q)), new Formula.Power(q, D(2))),
            Multiply(D(3), p)), Multiply(D(3), q)), D(2));
        return All("p", Integers(), All("q", Integers(), Arrow(LessEqual(D(0), p),
            Arrow(LessEqual(D(0), q), Equal(Multiply(D(2), count), polynomial)))));
    }

    private static Formula Distance(Formula v) => At(Qualified("SimpleGraph", "dist"),
        Local("teaGraph"), Typed(Triple(D(0), D(0), D(0)), Vertices()), v);
    private static Formula Coordinate(Formula v, int coordinate) => coordinate switch
    {
        1 => Seq(v, Dot, D(1)),
        2 => Seq(v, Dot, D(2), Dot, D(1)),
        _ => Seq(v, Dot, D(2), Dot, D(2)),
    };
    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Parenthesized(Seq(a, Comma, Sp, b, Comma, Sp, c));
    private static Formula Pairs() => Seq(Integers(), Sp, Times, Sp, Integers());
    private static Formula Vertices() => Seq(Integers(), Sp, Times, Sp, Parenthesized(Pairs()));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics", "TeaCoordinationSequence", name);
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
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
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
        At(Qualified("Int", "ediv"), Typed(left, Integers()), Typed(right, Integers()));
}
