using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineFiniteDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge sums on nine blocks of size nine.",
        H("Edge sums on nine blocks of size nine"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-label-bijection"),
            DeclarationHandle.Create(Module + ".edgeLabel_bijective"),
            H("Each group element labels one unordered edge"),
            StatementSource.FromAuthor(Disp(Seq(
                Mathrm, Grp(F.Id("edgeLabel")), Sp, Colon, Sp, Mathrm, Grp(F.Id("BlockEdge")),
                Sp, To, Sp, Mathrm, Grp(F.Id("LabelGroup")), Comma, Quad,
                Call("Bijective", Seq(Mathrm, Grp(F.Id("edgeLabel"))))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(
                "The input is a block t in the field with nine elements and an unordered pair of distinct vertices in the block. "
                + "The output is the sum of their labels in the product of two copies of the field and two binary coordinates. "
                + "The field coordinates fix the midpoint and the block for each displacement up to sign. "
                + "The binary coordinates distinguish the four displacement classes."))),
            DescribeRole.Theorem))));
}
