using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice;

internal sealed class NormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 NormalForm.", H("Integral physical NormalForm"),
        Blocks(
            Describe.Lean(DescribeId.Create("integral-normal-form"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/NormalForm.integral_normal_form"),
                H("integral normal form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consecutive actual carry equations establish doubling without extracting halves. The independent low generator and the two exceptional high generators retain the full original labels. Prefix sums and the four actual triple equations complete the five-generator presentation in every abelian group."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
