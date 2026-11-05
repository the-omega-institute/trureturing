using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: graph.",
        H("Double-hub graph"), Blocks(
            Paragraph(Text("The centre joins the two hubs and each hub joins its own m leaves. The edge range has cardinality 2m+2, while the vertex type has cardinality 2m+3. Paths through the hubs and centre prove connectivity. The edge-count characterization of a finite tree then proves the actual support graph is a tree.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubgraph-nonloop"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.nonloop"), H("nonloop"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem nonloop (m : \u2115) (e : Edge m) : src e \u2260 tgt e."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubgraph-actual-tree"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.actual_tree"), H("actual tree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines the explicitly constructed paths and edge bijection under the existing tree criterion. Exact source statement: theorem actual_tree (m : \u2115) : (graph m).IsTree."))), DescribeRole.Theorem))));
}
