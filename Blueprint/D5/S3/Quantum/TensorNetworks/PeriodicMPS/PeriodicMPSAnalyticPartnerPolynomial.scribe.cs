using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSAnalyticPartnerPolynomialDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticPartnerPolynomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic solutions of rescaled polynomial observations",
        H("Analytic solutions of rescaled polynomial observations"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsanalyticpartnerpolynomial-exists-polynomial-partner"),
                DeclarationHandle.Create(Module + ".exists_polynomial_partner"),
                H("Analytic solution from a leading system"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The polynomial equations in a real path parameter have analytic coefficient functions of the unknown parameters. Odd rows divide by the path parameter and even rows that vanish at zero divide by its square. The quotients extend analytically at zero and are even in the path parameter. A leading-system certificate gives the inverse derivative at the zero, so analytic inversion supplies an even analytic parameter curve that solves the original equations near zero."))),
                DescribeRole.Theorem))));
}
