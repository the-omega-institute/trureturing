using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cyclotomic.Stickelberger;

internal sealed class GaussSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauss Sums", H("Gauss Sums"),
        Blocks(
            Paragraph(Text("Valuations of Gauss sums, Jacobi-type quotients, distribution relation up to roots of unity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cyclotomic/Stickelberger/GaussSums.exists_jacobi_family"),
                H("exists_jacobi_family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Stickelberger: for B above p, some J : ℚ/ℤ → ℚ̄^× satisfies, if M ∣ p−1 and Mx = 0: σJ(x) = J(cyc_M(σ)x); J(x) is a unit off p, of order floorDiff c x at B, of absolute value 1 in all complex embeddings; J(x+b)/J(x) ≡ 1 above primes q ∣ p−1 if qb = 0; ∏_{b mod r} J(x+b/r)/J(rx) is a root of unity for r ∣ M prime to c.")))))));
}
