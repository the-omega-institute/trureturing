using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class StrictPeakAnalyticLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic obstacle estimate gives a sharp lower surface for bounded peak tails.",
        H("A Lower Surface for Peak Tail Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("bounded-tail-lower-surface"),
            DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/StrictPeakAnalyticLower.bounded_tail_lower_surface"),
            H("The refined analytic inequality"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let G be a real function on [0,1], with G and its square interval integrable. Assume pointwise that 0<=G(u)<=(1-u^2)/2. Put X equal to its integral, kappa equal to the integral of its square, and Delta=(1-X)kappa-X^2. Then 0<=X<=1/3. There is a unique s in [0,1] with s^3=1-3X.")),
                Paragraph(Text("The lower bound is Delta+X/15 >= (s^3/45)(1-s)(1+s+7s^2-3s^3-3s^4) >= 0. In particular Delta>=-X/15. If 0<X<1/3, the inequality Delta>-X/15 is strict. The statement retains the nonnegative cubic root as an existential variable; it does not require a particular implementation of real roots.")),
                Paragraph(Text("For H(u)=(1-u^2)/2-G(u), let h be its integral, b the integral of H squared, and c the integral of u squared times H. Expanding both moments gives Delta=-1/45+2h/15+(2/3+h)(b+c)-2h^2. Completing the square below u=s and using H>=0 above s gives b+c>=s^2h-2s^5/15. Substitution of s^3=3h gives the displayed correction. The remaining polynomial is at least 1+s+s^2 throughout [0,1].")),
                Paragraph(Text("This is an analytic theorem about tails. To apply it to a probability source, its first and second moment identities and the pointwise tail envelope must be established for that same source. The inequality alone does not provide that correspondence."))),
            DescribeRole.Theorem))));
}
