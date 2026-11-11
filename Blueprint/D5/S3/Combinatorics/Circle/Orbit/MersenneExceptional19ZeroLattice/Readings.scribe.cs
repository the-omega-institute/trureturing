using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice;

internal sealed class ReadingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 Readings.", H("Integral physical Readings"),
        Blocks(
            Describe.Lean(DescribeId.Create("integral-read"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Readings.integral_read"),
                H("integral read"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three binary words are evaluated using the original first, middle and last block functions. All floors and divisions are in integer coefficients. Finite sums and integer scalar multiplication transport the formulas to arbitrary abelian groups, including groups with torsion."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
