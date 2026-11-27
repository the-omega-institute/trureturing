using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class QuadFieldSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quad Field Splitting", H("Quad Field Splitting"),
        Blocks(
            Paragraph(Text("Primes and residue degrees, Frobenius on quadratic integers, lifting the exponent at 2. Decomposition of rational primes in Q(√-d) by the Legendre symbol.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/QuadFieldSplitting.prime_inert_or_eq_mul"),
                H("prime_inert_or_eq_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let d ≡ 3 mod 4 and let w lie above the prime p in K = ℚ(√−d). For some J the primes above p are w and J, and either J = w, Nw = p², or Nw = NJ = p, (p) = wJ.")))))));
}
