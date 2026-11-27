using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class TransversalNineLabelsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint sums on three blocks of size nine.",
        H("Three blocks of order nine"),
        Blocks(Describe.Lean(
            DescribeId.Create("triple-edge-label-bijection"),
            DeclarationHandle.Create(Module + ".edgeLabel_bijective"),
            H("The endpoint sums biject onto the label group"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("Bijective", Seq(Mathrm, Grp(F.Id("edgeLabel")))), Comma, Quad,
                Mathrm, Grp(F.Id("edgeLabel")), Colon, Quad,
                Mathbb, Grp(F.Id("Z")), Slash, D(3), Times,
                Call("Edge", new Formula.Subscript(Seq(Mathbb, Grp(F.Id("F"))), D(9))),
                To, new Formula.Subscript(Seq(Mathbb, Grp(F.Id("F"))), D(9)), Times,
                Mathbb, Grp(F.Id("Z")), Slash, D(3), Times,
                new Formula.Power(Seq(Open, Mathbb, Grp(F.Id("Z")), Slash, D(2), Close), D(2))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(
                "An edge consists of a block index modulo three and an unordered pair of distinct vertices in that block. "
                + "Its endpoint sum has 108 possible values. The field coordinate fixes the midpoint. For each possible "
                + "half-difference up to sign, the coordinate modulo three fixes the block. The two binary coordinates "
                + "distinguish the four possible half-differences. This bijection supplies the edge labeling used in the gluing construction."))),
            DescribeRole.Theorem))));
}
