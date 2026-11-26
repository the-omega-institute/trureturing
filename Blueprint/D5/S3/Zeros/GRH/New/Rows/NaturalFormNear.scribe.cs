using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class NaturalFormNearDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural Form Near", H("Natural Form Near"),
        Blocks(
            Paragraph(Text("The carrier is non-zero, of level one, rapidly decreasing and holomorphic. Combinations of twist-free theta forms approximate a fixed test function at points away from the cusps (first minimum bounded below).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/NaturalFormNear.exists_fNatural_approx"),
                H("exists_fNatural_approx"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 1 ≤ j ≤ m and ν = Data.nStar there are a bounded K₀ and ε with 4ε(5b)^{7ν} + ε < |K₀(1)| such that, whenever λ(g) ≥ (5b²⁴)^{−1/2} (Space.firstMinimum), some combination ∑_a c_a(g)F♮_a(gy) of the Data.fNatural is within ‖y‖^{6ν}ε of K₀(y) for all archimedean y.")))))));
}
