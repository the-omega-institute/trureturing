using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class RegularParentChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An analytic lift in the original source coordinates",
        H("RegularParentChart"),
        Blocks(
        Paragraph(Text("Write Lambda for parentLambda and B(b)=6/(1+b)-2/(1+2b). On the regular parent the drift increment is e=-(24/5)(b-1/8)B(b)/Lambda(r,b). For independent coordinates x=(t,b), set r=tb and reconstruct the same whole cubic by parentGain(r,b,e). Encoding its samples as ordinary polynomial coefficients gives chartWorld(x). The eight entries of chartSource are exactly r,b,r(1-r)/b,d and the four ordinary coefficients. The two entries of chartRead are the fifth response p and the actual eighth M response of this one world, at absolute clock eight.")),
        Paragraph(Text("For 9005/10000 <= r <= 9006/10000 and 12758/100000 <= b <= 12759/100000, j=b+r(1-r)/b is less than 83/100 and n=j+r is less than 1731/1000. Positive denominators then give Lambda < 0 by rational division inequalities. Thus the reconstructed drift has a nonzero denominator throughout this strip. All other denominators are positive at strict sources.")),
        Paragraph(Text("The lift is analytic, includes all five literal history equations and the nonzero whole polynomial, and exhausts every original parent world with the same r and b. This is a chart of the original parent, including its ordinary coefficient topology; it is not a change of the eight coordinate norm. Recovering t=r/b gives the original independent source coordinate. Analyticity also holds for both actual read functions.")),
        Paragraph(Text("The strip assertion alone identifies no algebraic center. Applying this chart at the exact critical world requires its independent algebraic definition and source enclosures. On this source strip, the polynomial derivative estimate and the inverse function theorem give a local inverse of (p,f_M), with a convex image neighborhood and a finite bound for the derivative of the complete source lift.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-regular-strip-denominator"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/RegularParentChart.strip_denominator"),
            H("The regular strip denominator"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real r and b with 9005/10000 <= r <= 9006/10000 and 12758/100000 <= b <= 12759/100000, parentLambda(r,b) is strictly negative."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-analytic-original-parent-chart"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/RegularParentChart.analytic_original_parent_chart"),
            H("analytic original parent chart"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every x=(t,b) whose r=tb and b satisfy the displayed closed rational strip bounds, chartWorld(x) belongs to OriginalParent. The maps chartWorld, chartSource and chartRead are real analytic at x. Every original parent W with W.r=tb and W.b=b equals chartWorld(x). Its original fifth and sixth response pair equals response(chartCoordinates(x)), and its recovered quotient r/b is t."))),
            DescribeRole.Theorem))));
}
