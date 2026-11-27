using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Analytic.Primes;

internal sealed class AuxiliaryPrimesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary Primes", H("Auxiliary Primes"),
        Blocks(
            Paragraph(Text("A prime 1 modulo M^k with logarithm in a long window; zero-free disc.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Analytic/Primes/AuxiliaryPrimes.exists_prime_modEq_one_log_mem"),
                H("exists_prime_modEq_one_log_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let M > 0 be a multiple of 4 and A natural. For large W, all k ≥ 2 with M^k ≤ W^A and all U in [W, W^A], there is a prime p ≡ 1 mod M^k with U ≤ log p ≤ U + W.")))))));
}
