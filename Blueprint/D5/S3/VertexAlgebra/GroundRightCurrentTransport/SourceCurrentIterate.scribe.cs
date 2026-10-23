using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class SourceCurrentIterateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original source current iterate", H("SourceCurrentIterate"), Blocks(
            Describe.Lean(DescribeId.Create("source-current-iterate-slice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate.source_current_iterate_slice"), H("source_current_iterate_slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The source upper bound is at most the supplied cutoff K. All source states, signed physical lifts and signed current/residue modes remain arbitrary. The source state-field iterate has separate finite supports: the original source-field tail gives range((K-r).toNat), and the positive-current tail gives range(vectorFrequencyBound b+1). Mapping each source coefficient through the linear actual physical-slice map preserves both sums and the original epsilon sign. The resulting complete field equality is consumed by the native first-source current step."))), DescribeRole.Theorem))));
}
