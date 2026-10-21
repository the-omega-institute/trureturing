using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class EigenbasisBlocksDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/EigenbasisBlocks.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local eigenbasis change exposes positive classical blocks with the exact marginal eigenvalue weights.",
        H("Local eigenbasis blocks"), Blocks(
            Describe.Lean(DescribeId.Create("subentropy-local-conjugate"),
                DeclarationHandle.Create(Owner + "localConjugate"),
                H("A local change of coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For matrices U on A and M on A×B, localConjugate U M is (U-adjoint tensor I) M (U tensor I). The first factor changes the coordinates on A and the second factor acts as the identity on B. This matrix is consumed by eigenbasis_blocks and the subadditivity proof."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subentropy-eigenbasis-blocks"),
                DeclarationHandle.Create(Owner + "eigenbasis_blocks"),
                H("Positive blocks and their marginal weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let M be any positive semidefinite matrix on A×B. Choose the eigenvector unitary U of partialTraceRight M, set K=localConjugate U M and define Y_x as K's diagonal B block at x. Then K is positive semidefinite, tr K=tr M, every Y_x is positive semidefinite, Σ_x Y_x=partialTraceLeft M, and tr Y_x is the corresponding real eigenvalue of partialTraceRight M. Block pinching of K has precisely these diagonal blocks and zero off-diagonal blocks.")),
                    Paragraph(Text("The entry identity expands the Kronecker products and matrix products. Tracing over B transports the first marginal by U-adjoint and U. Tracing over A instead gives the cyclic trace of U-adjoint S U for each fixed B entry, so unitarity preserves the opposite marginal. Positivity follows from conjugation and principal submatrices. The diagonalized first marginal gives the block traces. Zero blocks and repeated marginal eigenvalues require no division or choice of normalized conditional states."))),
                DescribeRole.Theorem))));
}
