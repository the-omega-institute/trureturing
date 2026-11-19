using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionTentObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous interval map has bounded folding depth.",
        H("DendriteObstruction - TentObstruction"), Blocks(
        Describe.Lean(DescribeId.Create("tent-half"),
            DeclarationHandle.Create(Owner + "continuumTent_half"),
            H("Two inverse branches of the tent map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t in the closed unit interval, the tent map min(2t,2-2t) sends both t/2 and 1-t/2 to t. These two affine branches are the formulas used to paste the successive folding functions."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("no-unbounded-tent-lifts"),
            DeclarationHandle.Create(Owner + "no_unbounded_tent_lifts"),
            H("A continuous interval map has bounded folding depth"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let h be continuous on the closed real unit interval. It is impossible that, for every natural depth m, h equals the m-fold tent iterate of a continuous u on that same interval with u(0)=0 and u(1)=2/3.")),
                Paragraph(Text("At the dyadic grid j/2^m, the m-fold tent iterate equals the parity of j. First hitting times of increasing levels form a strictly increasing family, by the intermediate value theorem and compact minimum attainment. Arbitrarily deep lifts therefore give arbitrarily many consecutive alternating values zero and one of the fixed function h. Uniform continuity separates successive times by a fixed positive distance. Summing these gaps exceeds the length of the unit interval."))), DescribeRole.Theorem))));
}
