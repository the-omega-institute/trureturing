using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSRealPolynomialZerosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRealPolynomialZeros";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module,
            "Relatively prime complex equations have a real common zero set covered in codimension two.",
            "static-algebraic-identifiability",
            Anchor.ParseCanonical("lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSMonicLevelGraphs")),
        H("Real graph covers for two polynomial equations"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsrealpolynomialzeros-result"),
            DeclarationHandle.Create(Module + ".cover_real_common_zeros"),
            H("Real graph covers for two polynomial equations"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Relatively prime complex polynomials give a differentiable cover of their real common zeros by domains of codimension two."))),
            DescribeRole.Theorem))));
}
