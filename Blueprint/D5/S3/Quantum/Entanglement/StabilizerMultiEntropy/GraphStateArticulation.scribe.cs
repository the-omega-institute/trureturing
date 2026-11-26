using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateArticulationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateArticulation.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared graph-state vertex has one exact rank increment and two normalized sampling channels.",
        H("Articulation gluing of physical graph-state moments"),
        Blocks(Describe.Lean(DescribeId.Create("physical-articulation-readout"),
            DeclarationHandle.Create(Owner + "physical_articulation_readout"),
            H("The reduced trace factors across a common vertex"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Gce),
            Blocks(
                Paragraph(Text("Let two finite simple binary adjacency charts meet at exactly one vertex. For an arbitrary cut, h1 and h2 are the actual reduced trace moments after deleting the vertex in each chart, and g1 and g2 are the moments retaining it. The glued trace splits into the product of the deletion moments and the product of the surplus moments gi minus x hi, with x equal to two to the power one minus the real order K.")),
                Paragraph(Text("The common vertex adds a single row or column. Removing it leaves two diagonal blocks; restoring it raises the rank precisely when its border in at least one block lies outside that block's row or column span. The existing graph-state spectrum converts this Boolean OR into the displayed physical trace identity. This uses no approximation.")),
                Paragraph(Text("If the two normalized surplus channels and the two deletion channels admit classical laws, independent samples and XOR at the common vertex give the composed law. The readout table varies with the real order, while a constant readout of two violates the articulation identity. The theorem does not itself assert that each constituent channel has a law."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var g1 = F.Id("g1");
        var g2 = F.Id("g2");
        var h1 = F.Id("h1");
        var h2 = F.Id("h2");
        var x = F.Id("x");
        var oneMinusX = new Formula.Binary(Num(1), FormulaBinaryOperator.Subtract, x);
        var a = new Formula.Binary(g1, FormulaBinaryOperator.Subtract, Seq(x, h1));
        var b = new Formula.Binary(g2, FormulaBinaryOperator.Subtract, Seq(x, h2));
        var numerator = Seq(Open, a, Close, Open, b, Close);
        return Disp(Equal(F.Id("G"), new Formula.Binary(Seq(x, h1, h2),
            FormulaBinaryOperator.Add, new Formula.Fraction(numerator, oneMinusX))));
    }
}
