using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class MarkedRibbonStateActionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A greedy forest made from genuine four-flag band switches.", H("A greedy forest made from genuine four-flag band switches"),
        Blocks(Describe.Lean(DescribeId.Create("actual-marked-forest"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonStateActions.marked_forest_state"),
            H("A greedy forest made from genuine four-flag band switches"),
            StatementSource.FromAuthor(Disp(Call("ExactOperationalStateEquivalence"))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("An unselected marked band is activated exactly if it joins different current boundary components. The simultaneous signed actions on its four distinct flags match the proved parity switch. The resulting numbered chart has exact port membership and pairing signs. These are used to compare the original state count to the signed interlacement count without a supplied chart."))), DescribeRole.Theorem))));
}
