using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "AR-labelings pull back along graph isomorphisms.",
        H("Transport of additive rigidity"),
        Blocks(Describe.Lean(DescribeId.Create("isomorphism-transport"),
            DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport.ar_graph_of_iso"),
            H("Pullback of an AR-labeling"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("Isomorphic", F.Id("G"), F.Id("H")), Sp, Land, Sp,
                Call("IsARGraph", F.Id("H")), Sp, Implies, Sp,
                Call("IsARGraph", F.Id("G"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let G and H be simple graphs on finite vertex types. If they are isomorphic "
                + "and H has an AR-labeling onto the integers from one through its edge count, "
                + "then G has such an AR-labeling. Pull back the label of an edge along the "
                + "isomorphism-induced edge map. This map is a bijection of edge sets and "
                + "preserves incidence. It also sends distinct subsets of an incidence set "
                + "to distinct subsets while preserving their label sums."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs"))]));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
