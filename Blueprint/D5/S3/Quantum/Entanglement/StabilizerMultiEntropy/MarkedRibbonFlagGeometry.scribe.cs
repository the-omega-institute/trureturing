using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class MarkedRibbonFlagGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal matching switches merge precisely the intended boundary components.", H("Literal matching switches merge precisely the intended boundary components"),
        Blocks(Describe.Lean(DescribeId.Create("guarded-matching-join"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonFlagGeometry.match_switch_join"),
            H("Literal matching switches merge precisely the intended boundary components"),
            StatementSource.FromAuthor(Disp(Call("ExactOperationalStateEquivalence"))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Before a switch, deleting one edge of the second matching in either old cycle cannot split that cycle: a proposed cut would be paired by the first involution, but paired by the second involution except at exactly one marked point. The opposite parity is impossible. This parity fact, together with the genuine dihedral cycle coordinates, is a live input to the marked ribbon chart construction."))), DescribeRole.Theorem))));
}
