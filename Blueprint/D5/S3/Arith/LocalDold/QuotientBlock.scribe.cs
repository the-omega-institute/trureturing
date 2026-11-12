using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class QuotientBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quotient and normalized block ideal correspondence", H("The unitriangular block pairing"), Blocks(
            Paragraph(Text("This proves the integer ideal correspondence in the proof of manuscript Lemma 3.1. The quotient, remainder coefficients and impulse sequence are actual objects, with no equivalence supplied as a hypothesis. Nonconstant coordinates are listed in reverse order k-1,...,1; row j is the top-coefficient observation against x^j. Its matrix is lower triangular with diagonal one. The integer inverse therefore preserves the generated ideal. No nonzero trailing coefficient or irreducibility is required for this correspondence; scalar-return existence is now proved below; exact p-adic lifting remains a separate obligation. Source attribution and the full incomplete family are in "), Ref("D5/L/Scale/jaidee2026blockdold"), Text(".")),
            Describe.Lean(DescribeId.Create("quotientblock-observation-ideal"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/QuotientBlock.observation_ideal"),
                H("observation_ideal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every integer recurrence of order k>=2 and every element q of its actual monic quotient, the k-1 values L(q*x^j), 0<=j<k-1, generate exactly the same ideal of Z as the nonconstant canonical-remainder coefficients of q. This is proved using the actual quotient power basis and a determinant-one pairing matrix, rather than assuming invertibility or block equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quotientblock-block-coefficient-ideal"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/QuotientBlock.block_coefficient_ideal"),
                H("block_coefficient_ideal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every natural n, the actual impulse block U(n),...,U(n+k-2) and the nonconstant remainder coefficients of x^n generate the same integer ideal. The consumer applies observation_ideal to x^n and uses the previously checked identity L(x^m)=U(m). Integer divisibility by any modulus is consequently the same on both lists. The separate rank theorem below identifies scalar returns at primes not dividing the constant coefficient. Valuation lifting and positive-block hypotheses are not assumed or proved by this ideal endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quotientblock-block-rank"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/QuotientBlock.block_rank"),
                H("block_rank"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every integer linear recurrence of order at least two and every prime p not dividing its characteristic polynomial constant coefficient, there is a positive r such that p divides every term of the actual order-minus-one impulse block at n if and only if r divides n, simultaneously at every natural index. The proof base-changes the actual monic quotient, proves that the root is a unit, forms the finite unit group modulo scalar units, and takes the order of the root class. Vanishing of all nonconstant remainder coefficients is proved equivalent to being scalar; the checked ideal bridge then gives actual block divisibility. No rank, desired block equivalence or recurrence identity is supplied as a hypothesis. Transient exact applications check Fibonacci and the cubic recurrence with ascending coefficients (-1,2,2), at every prime. The characteristic polynomial constant coefficient is checked to equal the negative of the ascending coefficient at zero, which is manuscript c_k. This general result applies to different orders and arbitrary signed coefficients; it assumes neither irreducibility nor a splitting-field parametrization. Exact odd/2-adic lifts and density are still open."))), DescribeRole.Theorem))));
}
