using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class WeightedBinaryEffectOptimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted interval of positive two-by-two effects has an exact nonlinear clipped-overlap optimum.",
        H("Exact weighted binary-effect optimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-binary-effect-optimum"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum.result"),
            H("The sharp two-piece loss in a positive matrix interval"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take D=diag(a,b), with 0<b<=a and a^2+b^2=1, and w between zero and one half. Vary H with H and D-H positive semidefinite. Clip tr(H^2) at w and tr((D-H)^2) at 1-w. Twice one minus the sum of the clipped values has the stated minimum, and the theorem constructs H attaining it.")),
                Paragraph(Text(
                    "At fixed L=tr(DH), the two positive determinants bound tr(H^2) from above by the smaller of two quadratics in U=tr(H). One increases up to U=(L+ab)/(a+b); the other decreases above it. Thus the middle frontier is attained by two complementary rank-one terms. The two exterior ranges are bounded sharply by the positive trace-square inequality and a one-direction diagonal filter.")),
                Paragraph(Text(
                    "Set q=b^2. Below q the two cap crossings compete and the larger of w/q and 1-w/q gives the smaller deficit. Above q, the larger target cap is saturated on the middle arc. This exact finite-matrix result is used by the native channel theorem.")))))));
}
