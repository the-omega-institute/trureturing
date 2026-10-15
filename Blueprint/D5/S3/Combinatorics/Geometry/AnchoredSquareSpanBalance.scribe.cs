using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class AnchoredSquareSpanBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anchored square partitions have exact difference-span, missing-membership and endpoint balances.",
        H("Complete span and endpoint balance"), Blocks(
            Paragraph(Text("A square of side q consists of all ordered pairs (a,b) with both coordinates in Fin q. An attained label t names the class containing (t,t). Every cell belongs to exactly one label, and no class contains two cells with the same signed difference a-b. These conditions admit arbitrary class sizes and coordinate orders.")),
            Node("Cell", "The complete square", "Cell(q) is Fin q times Fin q. The first coordinate is a and the second is b."),
            Node("difference", "Signed original difference", "For every square cell x=(a,b), difference(x) is the integer a-b, with both coordinates cast to the integers before subtraction."),
            Node("Cover", "One simultaneous cover", "Cover(q) consists of a total label map from the complete square to Fin q, the equations label(t,t)=t for every t, and injectivity of the pair (label(x),difference(x)). Its fibers are pairwise disjoint and cover the square; the diagonal equations make every label attained. Conversely a disjoint complete cover with one diagonal anchor per class and injective differences supplies this label map."),
            Node("cells", "Whole classes", "For every C:Cover(q) and t:Fin q, cells(C,t) is the finite set of all square cells labeled t."),
            Node("occupied", "Occupied differences", "For every C and t, occupied(C,t), denoted D(t), is the image of cells(C,t) under difference. It contains zero, and its cardinality equals the cardinality of that entire class."),
            Node("lower", "Lower occupied endpoint", "For every C and t, lower(C,t), denoted L(t), is the minimum of D(t). Its range is 1-q through zero."),
            Node("upper", "Upper occupied endpoint", "For every C and t, upper(C,t), denoted U(t), is the maximum of D(t). Its range is zero through q-1."),
            Node("size", "Class cardinality", "For every C and t, size(C,t), denoted m(t), is the integer cast of the cardinality of cells(C,t)."),
            Node("defect", "The inherited size defect", "For every C and t, defect(C,t), denoted delta(t), is 19-m(t). The balance theorem does not assume this value is nonnegative."),
            Node("gap", "Missing integers in one span", "For every C and t, gap(C,t), denoted g(t), is U(t)-L(t)+1-m(t). It is exactly the number of integers in the closed interval from L(t) to U(t) that are not in D(t)."),
            Node("totalGap", "Total class gaps", "For every C, totalGap(C), denoted G, is the sum of g(t) over all t:Fin q. Missing integers are counted separately for each class."),
            Node("supplied", "Classes supplying one difference", "For every C and integer j, supplied(C,j) is the set of labels t for which j belongs to D(t)."),
            Node("spanning", "Classes spanning one integer", "For every C and integer j, spanning(C,j) is the set of labels t for which L(t) is at most j and j is at most U(t)."),
            Node("missing", "Missing class memberships", "For every C and integer j, missing(C,j) is the subset of spanning(C,j) whose classes do not contain the occupied difference j. Such a membership is not an uncovered cell."),
            Node("spanCount", "Span incidence", "For every C and integer j, spanCount(C,j), denoted nu(C,j), is the integer cardinality of spanning(C,j)."),
            Node("holeCount", "Gap incidence", "For every C and integer j, holeCount(C,j), denoted h(C,j), is the integer cardinality of missing(C,j)."),
            Node("starts", "Lower endpoint incidence", "For every C and integer j, starts(C,j), denoted A(C,j), counts labels t with L(t)=j."),
            Node("ends", "Upper endpoint incidence", "For every C and integer j, ends(C,j), denoted B(C,j), counts labels t with U(t)=j."),
            Describe.Lean(DescribeId.Create("complete-span-endpoint-balance"),
                DeclarationHandle.Create(Prefix + "complete_span_endpoint_balance"),
                H("All span and endpoint identities"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The assertion ranges over every natural q and every C:Cover(q); in particular it includes all positive side lengths. In the formula L(C,t), U(C,t), delta(C,t), g(C,t), and G(C) denote the definitions above. The functions low(C,k) and high(C,k) count, respectively, labels with -L(t)<k and U(t)<k. The finite sum of h over Icc(1-q,q-1) is its sum over all integers, because the displayed support assertion proves that every other summand is zero.")),
                    Paragraph(Text("For a nonnegative difference k<q, its band is in bijection with Fin(q-k): send i to (i+k,i). Swapping the coordinates gives the corresponding negative band. Sending a band cell to its actual label is another bijection, since complete coverage supplies the label and difference injectivity separates the cells. Thus exactly q-|j| labels supply difference j. Every span incidence is either one of these supplied memberships or a missing membership, which gives the first equation and the bound on h.")),
                    Paragraph(Text("Zero belongs to every occupied set. An extreme difference lying in a span must equal its occupied endpoint, so the three boundary hole counts vanish. Counting the missing pairs (t,j) in the two orders gives G. Below zero no span ends, and above zero no span begins; successive span incidences therefore differ by the appropriate endpoint incidence. These statements include endpoints at zero, where a singleton span contributes to both A and B. At 1-q and q-1 the adjacent outside incidence is zero.")),
                    Paragraph(Text("The per-class identity follows from the actual span length and class cardinality. The complete partition contains q squared cells, so summing subtracts exactly q class baselines and yields q(q-1)+G. Subtracting the positive or negative span incidence from q gives both cumulative endpoint balances.")),
                    Paragraph(Text("For the native-alpha recut covers, take the actual original pair (a,b), the diagonal anchor label t, and the entire class C(t). Every cover of either lag family has the three geometric properties in Cover(q), so this theorem gives the complete span and endpoint conclusion on that whole domain, including fused nonmonotone classes and every defect allocation at eighteen labels. At q=18 the total is 306+G; at q=19 it is 342+G. No native service existence, cover existence, controller bound, or physical cost follows from these necessary counting identities."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("square-span-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Binary(Formula a, FormulaBinaryOperator op, Formula b) =>
        new Formula.Binary(a, op, b);
    private static Formula Add(Formula a, Formula b) => Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Conjunction(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) result = And(clauses[i], result);
        return result;
    }
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);

    private static Formula TheoremFormula()
    {
        var q = V("q"); var c = V("C"); var j = V("j"); var t = V("t"); var k = V("k");
        Formula H(Formula x) => Call("h", c, x);
        var lowerBoundary = Sub(D(1), q); var upperBoundary = Sub(q, D(1));
        var within = Lt(Abs(j), q);
        var holes = Seq(Sum, Underscore,
            Grp(Seq(j, Sp, InMacro, Sp, Call("Icc", lowerBoundary, upperBoundary))), Sp, H(j));
        var spans = Seq(Sum, Underscore, Grp(Seq(t, Sp, InMacro, Sp, Call("Fin", q))), Sp,
            Par(Sub(Call("U", c, t), Call("L", c, t))));
        var body = Conjunction(
            All("j", Integer, Imp(within, Eq(Call("nu", c, j), Add(Sub(q, Abs(j)), H(j))))),
            Eq(H(D(0)), D(0)), Eq(H(lowerBoundary), D(0)), Eq(H(upperBoundary), D(0)),
            All("j", Integer, Imp(within, And(Le(D(0), H(j)), Le(H(j), Abs(j))))),
            All("j", Integer, Imp(Or(Lt(j, lowerBoundary), Lt(upperBoundary, j)), Eq(H(j), D(0)))),
            Eq(Call("G", c), holes),
            All("j", Integer, Imp(And(Le(lowerBoundary, j), Le(j, D(0))),
                Eq(Call("A", c, j), Sub(Add(D(1), H(j)), H(Sub(j, D(1))))))),
            All("j", Integer, Imp(And(Le(D(0), j), Le(j, upperBoundary)),
                Eq(Call("B", c, j), Sub(Add(D(1), H(j)), H(Add(j, D(1))))))),
            All("t", Call("Fin", q), Eq(Sub(Call("U", c, t), Call("L", c, t)),
                Add(Sub(D(1, 8), Call("delta", c, t)), Call("g", c, t)))),
            Eq(spans, Add(Binary(q, FormulaBinaryOperator.Multiply, upperBoundary), Call("G", c))),
            All("k", Integer, Imp(And(Lt(D(0), k), Lt(k, q)), And(
                Eq(Call("high", c, k), Sub(k, H(k))),
                Eq(Call("low", c, k), Sub(k, H(Sub(D(0), k))))))));
        return Disp(All("q", Natural, All("C", Call("Cover", q), body)));
    }
}
