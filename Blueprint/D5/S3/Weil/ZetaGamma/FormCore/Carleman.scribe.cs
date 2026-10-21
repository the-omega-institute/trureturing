using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class CarlemanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex u and v satisfy MemLp 2 on the actual positive Lebesgue half-line. No double-integrability, row-bound or operator-bound premise is supplied. The actual r^(-1/2) row integral, weighted Young inequality, balancing and the zero-energy AE cases prove absolute integrability and the pi times product-of-L2-norms bound. This is the classical Carleman inequality, applied to the two endpoint corners.",
        H("Actual Gamma form core: Carleman"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-carleman-carleman-integrable-and-integral-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Carleman.carleman_integrable_and_integral_le"),
                H("carleman integrable and integral le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complex u and v satisfy MemLp 2 on the actual positive Lebesgue half-line. No double-integrability, row-bound or operator-bound premise is supplied. The actual r^(-1/2) row integral, weighted Young inequality, balancing and the zero-energy AE cases prove absolute integrability and the pi times product-of-L2-norms bound. This is the classical Carleman inequality, applied to the two endpoint corners."))),
                DescribeRole.Theorem))));
}
