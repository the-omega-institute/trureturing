using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class BoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative reciprocal Gamma Turanian coefficients at boundary shifts.",
        H("Every shift strictly between zero and one"), Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-gamma-boundary-second-negative"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Boundary.d_two_neg"),
                H("The second coefficient is strictly negative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t strictly between zero and one, the constant unit sequence at mu=-t and alpha=beta=t has a strictly negative second coefficient. Gamma recurrence evaluates this coefficient as 1-(1+t^2)/(t(1-t^2)Gamma(t)Gamma(1-t)). Euler reflection reduces its sign to a strict lower bound for sin(pi t).")),
                    Paragraph(Text("The finite Euler product is bounded below by (1-t^2)(1-t^2/4)(1+t^2/(n+2))/(1+t^2/2). The induction uses the exact difference u(1-u)/(a(a+1)^2) between (1+u/a)(1-u/(a+1)^2) and 1+u/(a+1), with u=t^2. Passing to the sine-product limit gives sin(pi t) at least pi t times (1-t^2)(1-t^2/4)/(1+t^2/2), which is strictly greater than pi t(1-t^2)/(1+t^2). This statement concerns degree two and does not assert a formula for every degree."))),
                DescribeRole.Theorem))));
}
