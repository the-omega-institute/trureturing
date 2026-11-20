using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/niu2026firstdescent");

    public DocumentDefinition Create()
    {
        var k = V("k");
        var n = V("n");
        var r = V("r");
        var t = V("t");
        var alpha = Alpha;
        var test = V("event");
        var rectangle = Call("StandardTableau", Call("rectangle", Add(k, D(1)), n));
        var descent = Call("rectangleDescent", k, n, t);
        var probability = Call("eventProbability", LambdaOf(t, rectangle, LeqOf(r, descent)));
        var statement = Settlement(k, n, r);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact uniform first-descent probabilities and the limiting law for every rectangular row count at least two.",
            H("Niu Question 15 for Rectangular Tableaux"),
            Blocks(
                Node("niuq15-eventprobability", "Uniform event probability", "eventProbability",
                    Equal(Call("eventProbability", test),
                        new Formula.Fraction(Cast(NatCard(new Formula.SetLiteral([
                            Seq(t, Colon, alpha, Sp, Mid, Sp, Apply(test, t))]))), Cast(Card(alpha)))),
                    "Here α is any finite type and event is a predicate on α. The casts take the two cardinalities to the real numbers.",
                    DescribeRole.Definition),
                Node("niuq15-rectangledescent", "Rectangle descent", "rectangleDescent",
                    Equal(descent, Seq(V("if"), Sp, V("hn"), Colon, Sp, Lt(D(0), n),
                        Sp, V("then"), Sp, Call("firstDescent", V("hn"), t), Sp, V("else"), Sp, D(0))),
                    "The shape has k + 2 rows and n columns. The positive-width branch supplies the proof hn of 0 < n. Its value is the one-based second-row first entry minus one.",
                    DescribeRole.Definition),
                Node("niuq15-rectangletailprobability", "Survival probability", "rectangleTailProbability",
                    Equal(Call("rectangleTailProbability", k, n, r), probability),
                    "The event is taken in the uniform sample of tableaux of the rectangle.", DescribeRole.Definition),
                Node("niuq15-rectanglepointprobability", "Point probability", "rectanglePointProbability",
                    Equal(Call("rectanglePointProbability", k, n, r),
                        Call("eventProbability", LambdaOf(t, rectangle, Equal(descent, r)))),
                    "The event fixes the descent at r.", DescribeRole.Definition),
                Node("niuq15-rectangleoddentryprobability", "Odd-entry probability", "rectangleOddEntryProbability",
                    Equal(Call("rectangleOddEntryProbability", k, n),
                        Call("eventProbability", LambdaOf(t, rectangle, Call("Odd", Add(descent, D(1)))))),
                    "At positive width the event is that the one-based entry in row two and column one is odd.",
                    DescribeRole.Definition),
                Node("niuq15-card-standardtableau-eq-shiftedcount", "Straight-shape cardinality",
                    "card_standardTableau_eq_shiftedCount",
                    All("k", NatType(), ImpliesFrom(LeqOf(D(2), k),
                        Parenthesized(All("shape", Call("RowShape", k), Equal(
                            Parenthesized(Seq(Cast(Card(Call("StandardTableau", V("shape")))),
                                Colon, Sp, Mathbb, Grp(V("Q")))),
                            Call("shiftedCount", Seq(V("shape"), Dot, V("rows")))))))),
                    "Both counts equal one at size zero. At positive size they sum over the same removable row ends. Strong induction on the number of cells gives equality.",
                    DescribeRole.Theorem),
                Node("niuq15-exactrectangletailcount", "Exact rectangle tail count", "exactRectangleTailCount",
                    All("k", NatType(), ExactCount(k, n, r)),
                    "The factors involving the bottom row change from 1 through k + 1 to r + 1 through r + k + 1. Their ratio is the binomial coefficient. The size and bottom-row factorials give the two descending factorials.",
                    DescribeRole.Theorem),
                Node("niuq15-question15", "The closed Question 15 proposition", "Question15",
                    new Formula.Logic(V("Question15"), FormulaLogicOperator.Iff, Parenthesized(statement)),
                    "The two distribution clauses quantify independently over natural thresholds. At r = 0 the limiting point mass is zero, so summing over all natural r gives the same normalization as summing over positive r.",
                    DescribeRole.Definition),
                Node("niuq15-rectanglequestion15", "First-descent law and odd-entry limit", "rectangleQuestion15",
                    statement,
                    "For K = k + 2 the survival limit is choose(r + K − 1, K − 1)/K^r, and the point limit is r choose(r + K − 1, K − 2)/K^(r + 1). The masses sum to one. Prefix rotation and the count identity give the finite tails. Their adjacent differences give the masses. A common summable bound permits the limit in the alternating parity sum.",
                    DescribeRole.Theorem)
            ), []));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Settlement(Formula k, Formula n, Formula r)
    {
        var rows = Add(k, D(2));
        var tail = All("r", NatType(), TendstoTo(
            LambdaOf(n, NatType(), Call("rectangleTailProbability", k, n, r)), Call("limitTail", rows, r)));
        var point = All("r", NatType(), TendstoTo(
            LambdaOf(n, NatType(), Call("rectanglePointProbability", k, n, r)), Call("limitMass", rows, r)));
        var normalization = Call("HasSum", Call("limitMass", rows), D(1));
        var ratio = new Formula.Fraction(Add(Cast(k), D(2)), Add(Cast(k), D(3)));
        var parity = TendstoTo(Call("rectangleOddEntryProbability", k),
            new Formula.Power(Parenthesized(ratio), rows));
        return All("k", NatType(), Seq(
            Parenthesized(tail), Sp, Land, Sp,
            Parenthesized(point), Sp, Land, Sp,
            Parenthesized(normalization), Sp, Land, Sp,
            Parenthesized(parity)));
    }

    private static Formula ExactCount(Formula k, Formula n, Formula r)
    {
        var rowIndex = Add(k, D(1));
        var shortCount = Card(Call("StandardTableau", Call("rotatedShape", rowIndex, n, r)));
        var fullCount = Card(Call("StandardTableau", Call("rectangle", rowIndex, n)));
        var longFactor = Call("descFactorial", Multiply(Parenthesized(Add(k, D(2))), n), r);
        var fullTerm = Multiply(Multiply(fullCount, Call("tailCoefficient", Add(k, D(2)), r)),
            Call("descFactorial", n, r));
        return All("n", NatType(), All("r", NatType(),
            ImpliesFrom(Lt(D(0), n), ImpliesFrom(LeqOf(r, n), Equal(Multiply(shortCount, longFactor), fullTerm)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Cast(Formula value) => Call("cast", value);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Card(Formula type) => Apply(Qualified("Fintype", "card"), type);
    private static Formula NatCard(Formula type) => Apply(Qualified("Nat", "card"), type);
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(variable, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula ImpliesFrom(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula TendstoTo(Formula sequence, Formula limit) =>
        Call("Tendsto", sequence, V("atTop"), Call("nhds", limit));
}
