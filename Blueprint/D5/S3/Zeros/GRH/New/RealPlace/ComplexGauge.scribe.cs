using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class ComplexGaugeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Gauge", H("Complex Gauge"),
        Blocks(
            Paragraph(Text("Tower measure at C is Haar with constant bound; level and gauge at C.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/ComplexGauge.exists_orthonormal_ker_lintegral_le"),
                H("exists_orthonormal_ker_lintegral_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let n = ϱ+1, |ι| = s+1+3n ≤ L, L ≥ 4, and rank C ≤ 3n. Some matrix O with orthonormal columns has CO = 0 and, for all j, the integral of (36/|Oᴴu|²)^s over the u in ℂ^ι with all |u_i| ≤ L^j is at most L^{198n(j+1)}.")))))));
}
