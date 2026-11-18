using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class FixedSizeCutVarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance of a uniformly sampled fixed-size weighted cut has two incidence contributions.",
        H("Variance of fixed-size weighted cuts"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-size-cut-variance"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Incidence/FixedSizeCutVariance.fixed_size_cut_variance"),
            H("The degree and zero-degree contributions"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take a finite vertex set of size n at least four and an integer m from two to n minus two. "
                    + "Each unordered edge receives an arbitrary real weight w. The sampled side S is uniform "
                    + "over the m-element subsets. The cut weight C is the sum over edges with exactly one endpoint in S.")),
                Paragraph(Text(
                    "Subtract the mean edge weight from each edge to get centered weights. For vertex i, let "
                    + "u(i) be the sum of its incident centered weights divided by n minus two. The residual z "
                    + "on edge {i,j} is its centered weight minus u(i) and u(j). The sum of the incident residual "
                    + "weights is zero at each vertex. Both sums in the formula range over unordered edges.")),
                Paragraph(Text(
                    "The two crossing indicators have different joint probabilities according to whether the "
                    + "edges coincide, meet at one vertex, or are disjoint. Counting the permitted placements of "
                    + "their endpoints gives the covariance in terms of unsigned incidence. Constants shift "
                    + "the cut by the same amount for every S. The remaining degree and residual weights are "
                    + "orthogonal, and their covariance contributions have the displayed coefficients.")),
                Paragraph(Text(
                    "When the two sides have equal size, the degree coefficient vanishes. The residual "
                    + "coefficient remains positive throughout the stated interval."))),
            DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));

    private static Formula Statement()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var i = F.Id("i");
        var j = F.Id("j");
        var twoM = Mul(D(2), m);
        var nMinusM = Parenthesized(Sub(n, m));
        var nMinusOne = Parenthesized(Sub(n, D(1)));
        var nMinusTwo = Parenthesized(Sub(n, D(2)));
        var nMinusThree = Parenthesized(Sub(n, D(3)));
        var degree = new Formula.Fraction(
            Mul(Mul(m, nMinusM), Square(Parenthesized(Sub(n, twoM)))),
            Mul(Mul(n, nMinusOne), nMinusTwo));
        var residual = new Formula.Fraction(
            Mul(Mul(Mul(Mul(D(4), m), Parenthesized(Sub(m, D(1)))), nMinusM),
                Parenthesized(Sub(Sub(n, m), D(1)))),
            Mul(Mul(Mul(n, nMinusOne), nMinusTwo), nMinusThree));
        var a = Seq(F.Id("u"), Parenthesized(i));
        var b = Seq(F.Id("u"), Parenthesized(j));
        var z = Seq(F.Id("z"), Parenthesized(Seq(i, Comma, j)));
        var edge = Grp(Seq(i, Lt, j));
        var degreeSum = Seq(F.Sum, Underscore, edge, Sp, Square(Parenthesized(Add(a, b))));
        var residualSum = Seq(F.Sum, Underscore, edge, Sp, Square(z));
        var variance = Seq(Operatorname, Grp(F.Id("Var")), Parenthesized(F.Id("C")));
        return Disp(new Formula.Relation(variance, FormulaRelationOperator.Equal,
            Add(Mul(degree, degreeSum), Mul(residual, residualSum))));
    }
}
