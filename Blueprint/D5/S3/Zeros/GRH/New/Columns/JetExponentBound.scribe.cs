using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class JetExponentBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jet Exponent Bound", H("Jet Exponent Bound"),
        Blocks(
            Paragraph(Text("Marked primes at inert p: orders of -p, parity, balance; scaled Hecke operator. Sum of jet exponents along the chain is at least gain minus error.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/JetExponentBound.sum_lowColumns_le"),
                H("sum_lowColumns_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For marked Λ and j < m: #Λ·δ_p + 𝔯·∑_σ Data.lowColumns j σ ≤ loss(p)/m + #(even tops)·a/x₁, the sum over the even places σ (those inducing a prime in Λ), with δ_p = Data.deltaP p.")))))));
}
