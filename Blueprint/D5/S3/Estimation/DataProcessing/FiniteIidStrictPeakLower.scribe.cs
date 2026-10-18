using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FiniteIidStrictPeakLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite independent strict peaks have a sharp determinant lower surface.",
        H("The Strict Peak Lower Surface for Finite Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-iid-lower-surface"),
            DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/FiniteIidStrictPeakLower.finite_iid_lower_surface"),
            H("The determinant bound and its equality cases"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be any finite linearly ordered alphabet, with arbitrary nonnegative real letter masses p summing to one. Use the independently specified five-fold product law and strict-peak classifier of IidStrictPeakSource. In the order null, low, high, both endpoints, middle, the induced masses are modeLaw(0),...,modeLaw(4). Write X=modeLaw(1)+modeLaw(3) and D=modeLaw(0)modeLaw(3)-modeLaw(1)modeLaw(2). The source theorem identifies all three peak occupancies with X.")),
                Paragraph(Text("Then 0<=X<1/3, and X=0 exactly when one letter has mass one and every other letter has mass zero. There is an s in [0,1] satisfying s^3=1-3X for which D+X/15 is at least (s^3/45)(1-s)(1+s+7s^2-3s^3-3s^4), and this correction is nonnegative. Consequently D>=-X/15 and D>-1/45. Equality D=-X/15 holds exactly for the point masses, where D=0. The joint mass kappa=modeLaw(3) also satisfies X-1/5<=kappa<=2/15.")),
                Paragraph(Text("For each letter i, put a(i)=sum of p(j) over j<i. The quantile-coordinate tail is the sum over i of p(i)a(i) times the indicator of u<=a(i). Its first moment is sum p(i)a(i)^2; its second moment is sum p(c)G(c)^2, with G(c)=sum over i>c of p(i)a(i). These equalities connect the actual source to the analytic determinant theorem.")),
                Paragraph(Text("A cutoff selects an upper segment of letters. The triangular square identity for its restricted masses bounds the tail by (1-u^2)/2. This supplies the analytic envelope without assuming a quantile coupling. Since the tail and the envelope sum to at most one, their squared-moment difference is bounded by their first-moment difference; this gives the two saturation estimates for kappa. The greatest letter of positive mass leaves a nonempty final quantile interval on which the tail is zero and the continuous envelope has positive integral; hence X<1/3. Vanishing X forbids two distinct positive-mass letters, yielding the exact point-mass equality criterion. Zero mass coordinates and ties remain within the statement."))),
            DescribeRole.Theorem))));
}
