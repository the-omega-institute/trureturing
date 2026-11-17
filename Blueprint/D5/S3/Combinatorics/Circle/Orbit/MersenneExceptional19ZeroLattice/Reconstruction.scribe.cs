using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice;

internal sealed class ReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 Reconstruction.", H("Integral physical Reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("reconstructed-normal-form"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Reconstruction.reconstructed_normal_form"),
                H("reconstructed normal form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two affine rows and the actual Q and 8Q indicators eliminate the five-generator presentation by integral Bezout identities. Only unit pivots are used in the group. The surviving generator therefore reconstructs every original physical coordinate without a rationalization premise."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
