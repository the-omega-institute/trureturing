using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.",
        H("Compatible response forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incoming-response-step"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step"),
                H("Incoming lifts respect response depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two states with the same numbered path responses at depth d plus one, lifting the same incoming base edge places their predecessor states in one depth-d response class. Appending that edge to each depth-d path identifies the resulting lifted paths with the original depth-(d+1) observations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incoming-response-fiber-card"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card"),
                H("Response classes preserve incoming counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Within one response class, choosing either representative gives the same number of actual incoming base edges whose lifted predecessor lies in any fixed response class. The edge identity is unchanged by the comparison, and response coherence identifies the two lifted quotient classes."))),
                DescribeRole.Theorem),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-square-column-lift-count"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count"),
                H("Square columns count incoming lifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At each pair of numbered R edges, the square-matrix entry equals the number of A edges entering the terminal R edge whose unique incoming square lift reaches the initial R edge. The proof identifies each matrix edge number with its actual square, reconstructs that square from its A edge and terminal R edge, and establishes a bijection with the lift fiber. Parallel edge identities are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-square-row-lift-count"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count"),
                H("Square rows count outgoing lifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Dually, each square-matrix entry equals the number of B edges leaving the initial R edge whose unique outgoing square lift reaches the terminal R edge. Reconstructing the inverse phi square from the B edge and initial R edge makes the equality a numbered-edge fiber bijection, not just an unnumbered support relation."))),
                DescribeRole.Theorem))));
}
