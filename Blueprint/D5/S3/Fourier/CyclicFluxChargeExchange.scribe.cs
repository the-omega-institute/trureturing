using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CyclicFluxChargeExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic modular matrix exchanges flux and insertion",
        H("The cyclic modular matrix exchanges flux and insertion"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-flux-charge-exchange"),
            DeclarationHandle.Create("D5/S3/Fourier/CyclicFluxChargeExchange.chargeTransform_modularS"),
            H("The cyclic modular matrix exchanges flux and insertion"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "For every positive modulus the normalized two-index kernel becomes a signed exchange after a positive Fourier transform in the charge coordinate. " +
                "The two transforms cancel by discrete Fourier inversion. " +
                "In the cyclic Barnes–Wall calculation the exchange takes the order-four twist with central insertion to the reflection twist with inverse insertion."))),
            DescribeRole.Theorem))));
}
