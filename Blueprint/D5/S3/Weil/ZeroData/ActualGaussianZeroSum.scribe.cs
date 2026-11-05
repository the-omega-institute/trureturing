using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualGaussianZeroSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute convergence of the complete shifted zero sum.",
        H("Absolute convergence of the complete shifted zero sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gaussian-e-summable"),
                DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualGaussianZeroSum.E_summable"),
                H("Absolute convergence of the complete shifted zero sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("E(m,gamma) is the sum over all actual occurrences of exp(m*((rho-i*gamma)^2+16*(rho-i*gamma))). No reciprocal weights occur in E itself. For m>=1 and any nonzero real eta, exp(-m*(eta-gamma)^2)<=(2+2*gamma^2)/eta^2. This follows by multiplying the elementary exponential bound by its inverse and using eta^2<=2*(eta-gamma)^2+2*gamma^2.")),
                Paragraph(Text("The actual strip 0<Re(rho)<1 contributes at most exp(17*m). Hence the summand norm is bounded by exp(17*m)*(2+2*gamma^2)*im(rho)^(-2). The actual inverse-square summability pays absolute convergence before the local/complement decomposition. This statement is consumed by ActualGaussianDirectTail.E_eq_local_add_omitted."))),
                DescribeRole.Theorem))));
}
