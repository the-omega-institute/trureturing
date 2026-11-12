using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class QuotientBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quotient and normalized block ideal correspondence", H("The unitriangular block pairing"), Blocks(
            Paragraph(Text("This proves the integer ideal correspondence in the proof of manuscript Lemma 3.1. The quotient, remainder coefficients and impulse sequence are actual objects, with no equivalence supplied as a hypothesis. Nonconstant coordinates are listed in reverse order k-1,...,1; row j is the top-coefficient observation against x^j. Its matrix is lower triangular with diagonal one. The integer inverse therefore preserves the generated ideal. No nonzero trailing coefficient or irreducibility is required for this correspondence; scalar-return existence and exact p-adic lifting remain separate obligations. Source attribution and the full incomplete family are in "), Ref("D5/L/Scale/jaidee2026blockdold"), Text(". Audit attempts and unfinished targets are disclosed under issue 29392.")),
            Describe.Lean(DescribeId.Create("quotientblock-observation-ideal"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/QuotientBlock.observation_ideal"),
                H("observation_ideal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every integer recurrence of order k>=2 and every element q of its actual monic quotient, the k-1 values L(q*x^j), 0<=j<k-1, generate exactly the same ideal of Z as the nonconstant canonical-remainder coefficients of q. This is proved using the actual quotient power basis and a determinant-one pairing matrix, rather than assuming invertibility or block equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quotientblock-block-coefficient-ideal"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/QuotientBlock.block_coefficient_ideal"),
                H("block_coefficient_ideal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every natural n, the actual impulse block U(n),...,U(n+k-2) and the nonconstant remainder coefficients of x^n generate the same integer ideal. The consumer applies observation_ideal to x^n and uses the previously checked identity L(x^m)=U(m). Integer divisibility by any modulus is consequently the same on both lists. The separate identification with scalar units at primes not dividing the trailing coefficient, rank existence, valuation lifting and positive-block hypotheses is not assumed or proved by this endpoint."))), DescribeRole.Theorem))));
}
