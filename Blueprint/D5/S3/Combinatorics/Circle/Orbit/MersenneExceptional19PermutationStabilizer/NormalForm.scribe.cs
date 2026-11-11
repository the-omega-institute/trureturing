using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer;

internal sealed class NormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 NormalForm.", H("Integral physical NormalForm"),
        Blocks(
            Describe.Lean(DescribeId.Create("triple-equations"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.triple_equations"),
                H("triple equations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four actual triple indicators give the low and high block equations. Consecutive G, F and H carry equations give doubling in the interior. The geometric prefix sum is proved by induction; the retained rational normal form is separate from the integral normal form consumed below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geom-sum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.geom_sum"),
                H("geom sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four actual triple indicators give the low and high block equations. Consecutive G, F and H carry equations give doubling in the interior. The geometric prefix sum is proved by induction; the retained rational normal form is separate from the integral normal form consumed below."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
