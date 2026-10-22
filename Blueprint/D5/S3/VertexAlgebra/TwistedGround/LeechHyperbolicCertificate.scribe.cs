using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class LeechHyperbolicCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal frame has twenty-four singular vectors and all hyperbolic polar pairings.",
        H("The Literal Hyperbolic Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leechhyperboliccertificate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate.literal_certificate"),
                H("The Literal Hyperbolic Certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The literal binary integer vectors reduce to the original lattice mod-two charge space. Each of the twenty-four half Gram norms reduces to zero; the 576 Gram pairings reduce to one exactly on partner pairs and zero otherwise.")),
                    Paragraph(Text("The original quadratic reduction identity transports the integer norm checks to the original cocycle diagonal. The original Gram reduction transports the polar checks to modTwoPairing. Evaluating a dependence against partner vectors then yields the hyperbolic basis used by the native representation construction."))),
                DescribeRole.Theorem))));
}
