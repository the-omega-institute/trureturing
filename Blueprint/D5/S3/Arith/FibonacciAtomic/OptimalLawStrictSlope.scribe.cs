using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawStrictSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var m = F.Id("m");
        var p = F.Id("p");
        var d = F.Id("d");
        var k = F.Id("k");
        var l = Call("L", p);
        var r = Call("R", Seq(p, Comma, d));
        var ratio = new Formula.Fraction(l, Call("p", k));
        var law = Call("PositiveLaw", Seq(m, Comma, p));
        var least = Call("LeastIndex", Seq(p, Comma, k));
        var simplex = Call("Simplex", Seq(m, Comma, p));
        var lawData = Seq(Forall, Sp, m, Comma, Sp, p, Comma, Sp,
            simplex, Sp, To, Sp, Open,
            Open, Forall, Sp, d, Comma, Sp, D(0), Sp, Le, Sp, r, Sp, Le, Sp, m, Close,
            Sp, Land, Sp, Call("Summable", Seq(d, Mapsto, new Formula.Fraction(r, new Formula.Power(D(2), d)))),
            Sp, Land, Sp, D(0), Sp, Le, Sp, l, Close);
        var costLower = Seq(Forall, Sp, m, Comma, Sp, p, Comma, Sp,
            Open, D(2), Sp, Le, Sp, m, Sp, Land, Sp, law, Close,
            Sp, To, Sp, D(1), Sp, Le, Sp, l);
        var infUpper = Seq(Forall, Sp, m, Comma, Sp, p, Comma, Sp, k, Comma, Sp,
            Open, law, Sp, Land, Sp, least, Close,
            Sp, To, Sp, Call("alpha", m), Sp, Le, Sp, ratio);
        var infLower = Seq(Forall, Sp, m, Comma, Sp, Open, D(2), Sp, Le, Sp, m, Close,
            Sp, To, Sp, m, Sp, Le, Sp, Call("alpha", m));
        var semicont = Seq(Forall, Sp, m, Comma, Sp, k, Comma, Sp,
            Call("LowerSemicontinuousOn", Seq(p, Mapsto, ratio, Comma, Call("PositiveSimplex", m))));
        var attainment = Seq(Forall, Sp, m, Comma, Sp, Open, D(2), Sp, Le, Sp, m, Close,
            Sp, To, Sp, Exists, Sp, p, Comma, Sp, k, Comma, Sp,
            law, Sp, Land, Sp, least, Sp, Land, Sp, Equal(ratio, Call("alpha", m)));
        var natural = Seq(Mathbb, Grp(F.Id("N")));
        var predecessor = Seq(Open, m, Sp, Minus, Sp, D(1), Close);
        var statement = Seq(
            Equal(Call("alpha", D(1)), D(0)), Sp, Land, Sp,
            Equal(Call("alpha", D(2)), D(2)), Sp, Land, Sp,
            Open, Forall, Sp, m, Colon, Sp, natural, Comma, Sp,
            Open, D(3), Sp, Le, Sp, m, Close, Sp, To, Sp,
            Call("alpha", predecessor), Sp, Lt, Sp, Call("alpha", m), Close);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The minimum ratio of dyadic sampling cost to least atom mass grows strictly with the label count.",
            H("Strict Growth of the Optimal Real-law Slope"), Blocks(
                Paragraph(Text("Simplex(m,p) means that p is a real vector indexed by Fin m with sum one; PositiveLaw adds strict positivity of every coordinate. PositiveSimplex(m) is the set of vectors satisfying PositiveLaw(m,p). LeastIndex(p,k) means p(k) is at most every coordinate. R(p,d) is 2^d minus the sum of the integer floors of 2^d p(i), and L(p) is the sum of R(p,d)/2^d over all natural depths. These definitions include terminating binary coordinates and all real probability laws.")),
                Describe.Lean(DescribeId.Create("law-data"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.law_data"),
                    H("Normalized floor tails"), StatementSource.FromAuthor(Disp(lawData)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The floor inequalities bound each residual between zero and the number of coordinates. Geometric domination makes the tail series summable and its sum nonnegative.")))),
                Describe.Lean(DescribeId.Create("cost-ge-one"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.cost_ge_one"),
                    H("The first charged bit"), StatementSource.FromAuthor(Disp(costLower)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("With at least two positive coordinates, every coordinate is below one. All depth-zero floors vanish, so the depth-zero contribution is one.")))),
                Describe.Lean(DescribeId.Create("alpha-le"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_le"),
                    H("Every law bounds the infimum"), StatementSource.FromAuthor(Disp(infUpper)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("All admissible ratios are nonnegative. The infimum is therefore at most the ratio of any particular positive normalized law.")))),
                Describe.Lean(DescribeId.Create("alpha-ge-labels"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_ge_labels"),
                    H("A lower bound from the least mass"), StatementSource.FromAuthor(Disp(infLower)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The least coordinate is at most 1/m and the cost is at least one. Every admissible ratio, and hence its infimum, is at least m.")))),
                Describe.Lean(DescribeId.Create("ratio-lower-semicontinuous"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.ratio_lower_semicontinuous"),
                    H("Lower semicontinuity on the positive simplex"),
                    StatementSource.FromAuthor(Disp(semicont)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("At a fixed law, finitely many floors cannot increase in a sufficiently small neighborhood. Every finite tail prefix supplies a local lower bound. Convergence of the nonnegative series and continuity of the positive denominator pass this bound to the full ratio.")))),
                Describe.Lean(DescribeId.Create("attained"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.attained"),
                    H("Attainment in the full real domain"), StatementSource.FromAuthor(Disp(attainment)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The uniform law supplies a finite comparison ratio. Since every multi-label law costs at least one, any smaller ratio has its least coordinate bounded away from zero. After relabeling this coordinate to a fixed index, optimization takes place on a nonempty compact subset of the real simplex. Lower semicontinuity supplies a minimum there, and laws outside it have larger ratio.")))),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result"),
                    H("Strict growth with the number of labels"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For a strictly positive normalized real law p on m labels, the dyadic cost is the sum over depths d of the unassigned floor remainder divided by 2^d. The function alpha is the infimum of this cost divided by the smallest mass. The domain contains all such real laws, without a rationality or finite-depth restriction.")),
                        Paragraph(Text("A single label has zero cost. For two labels, the cost is at least one and the smallest mass is at most one half. The uniform two-label law has cost one and attains ratio two.")),
                        Paragraph(Text("Take an attaining law with at least three labels. Merging two atoms never increases any floor remainder. If the smallest atom is unique, merging it with another atom strictly raises the new minimum mass. If two atoms have the same smallest mass, their first positive binary digit produces a strict carry one depth earlier, so merging them strictly reduces the convergent cost sum. In each case the new law has a strictly smaller ratio, proving the strict inequality for consecutive label counts.")))))));
    }
}
