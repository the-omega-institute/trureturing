using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic;

internal sealed class NearMaximumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Near Maximum", H("Near Maximum"),
        Blocks(
            Paragraph(Text("Rapidly decreasing holomorphic forms are large only away from cusps, explicit depth.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum.exists_near_max"),
                H("exists_near_max"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F ≠ 0 be rapidly decreasing, automorphic of level ς = −ς̄, Im Φ_wς ∈ (0,c], c ≥ 1, holomorphic of weight in [−B,B], B ≥ 2, gap 1. Some z has F(z) ≠ 0, |F| ≤ 2|F(z)|, and |F(g)| ≥ |F(z)| implies Space.firstMinimum(g) ≥ (Bc)^{−½}.")))))));
}
