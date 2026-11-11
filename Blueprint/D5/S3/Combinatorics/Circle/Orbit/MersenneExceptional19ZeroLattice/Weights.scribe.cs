using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice;

internal sealed class WeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 Weights.", H("Integral physical Weights"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-eq-scale-primitive"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Weights.source_eq_scale_primitive"),
                H("source eq scale primitive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source phases, the parameter equations and 19Q=B squared plus B plus one identify the literal source as 19(B-1) times its primitive weight at every original label. The explicit coordinate generator fixes the remaining arbitrary-group parameter by the integer identity -3a+2b=1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-reconstruction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Weights.integral_reconstruction"),
                H("integral reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source phases, the parameter equations and 19Q=B squared plus B plus one identify the literal source as 19(B-1) times its primitive weight at every original label. The explicit coordinate generator fixes the remaining arbitrary-group parameter by the integer identity -3a+2b=1."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
