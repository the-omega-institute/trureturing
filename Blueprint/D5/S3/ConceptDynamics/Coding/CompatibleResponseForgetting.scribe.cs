using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.",
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-square-right-forgetting"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting"),
                H("Compatible squares forget the right boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The inverse finite sweep applies each actual phi square backward along a numbered B path. The inverse of compatibility equation C identifies its terminal R edge with the terminal edge of psiB inverse, independently of the chosen initial R edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-square-graph"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections"),
                H("Finite essential square adjacency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The matrix entries count actual phi squares by their numbered R endpoints, with a finite equivalence between each entry number and its square fiber. Essential A and B edges supply incoming and outgoing squares at every R state. The psiA and psiB path bijections supply R edges above every A and B vertex, so both endpoint projections are surjective."))),
                DescribeRole.Theorem))));
}
