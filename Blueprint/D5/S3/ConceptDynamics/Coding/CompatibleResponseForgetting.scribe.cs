using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible numbered path certificate constructs square lifts whose left boundary forgets after its lag.",
        H("Compatible response forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compatible-square-left-forgetting"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting"),
                H("Compatible squares forget the left boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For essential A and B and positive lag, the certificate gives endpoint-indexed bijections on actual numbered A-R, R-S, and S-R paths, plus the full compatibility equation on every A path and terminal R edge. Phi and its inverse construct incoming and outgoing squares whose boundary states are the original R edges. Induction identifies repeated incoming square lifts with the finite phi sweep. Compatibility then makes the initial R edge equal to the first edge of psiA inverse of the A path, independently of the terminal R edge."))),
                DescribeRole.Theorem))));
}
