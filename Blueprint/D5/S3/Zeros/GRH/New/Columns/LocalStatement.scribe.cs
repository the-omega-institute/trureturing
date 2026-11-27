using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class LocalStatementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Statement", H("Local Statement"),
        Blocks(
            Paragraph(Text("Scaled Hecke operator passes the chain; divisibility on its image at non-split primes. Explicit bound for all conjugates of the untwisted chain of lifts. Chain of lifts is divisible by predicted p-power on a submodule of small index.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/LocalStatement.exists_indexDvd_Bmu_divisible"),
                H("exists_indexDvd_Bmu_divisible"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an integer β < gain(p) − err(p) + 1 (err = Data.allowedLoss; gain omitted unless p < x₁ is non-split), some O_ι-module S of columns has index (IndexDvd) dividing p^l, l ≤ err(p)·dim, in the ι-integral columns, and v(B_μφ) ≥ β for ramified φ ∈ S, all twists with Q prime to p, all good Ψ.")))))));
}
