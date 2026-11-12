using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class NormalizedKBonacciDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized impulse k-bonacci arithmetic", H("Normalized impulse k-bonacci arithmetic"), Blocks(
            Paragraph(Text("The actual natural sequence is constructed with Mathlib LinearRecurrence.mkSol and impulse initial values 0,...,0,1. It is distinct from the positive seeds 1,...,1,2 in KBonacciShifts. These general infinite proofs supply Proposition 7.1 arithmetic and the parity/rank and first-block parts of Theorem 7.2. Full exact 2-adic lifting, least local repair k+1, uniform affine sample, generating function and companion trace/graph/zeta identities remain unproved here. No order 2-20 computation is substituted for these all-order results. Registration is unfinished under issue 29392.")),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-difference"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.difference"),
                H("difference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every positive order k and every m>=0, U(m+k+1)+U(m)=2U(m+k). The proof subtracts the two actual adjacent recurrence sums, without assuming the difference identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-term-parity"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.term_parity"),
                H("term_parity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every k>=2 and every n>=0, U(n) modulo two is zero precisely when n modulo k+1 is less than k-1, and is one otherwise. This is an infinite theorem, using the recurrence difference to prove the full parity period."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-block-even-iff"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.block_even_iff"),
                H("block_even_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every k>=2 and every n>=0, two divides the actual gcd of U(n),...,U(n+k-2) if and only if k+1 divides n. Thus the least positive mod-two block rank is k+1. This is a gcd theorem about the actual sequence, not a parameter called rank."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-positive-tail"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.positive_tail"),
                H("positive_tail"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every k>=2, U(n)>0 at every n>=k-1. The proof uses strong induction and a genuinely positive summand of the actual recurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-block-positive"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.block_positive"),
                H("block_positive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every k>=2 and every positive n, the actual k-1-term block gcd is strictly positive. Blocks before the positive tail contain the impulse value, and later blocks contain a positive term. Thus positive-index block valuations are finite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizedkbonacci-first-even-block"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedKBonacci.first_even_block"),
                H("first_even_block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every k>=2, the actual block gcd at n=k+1 equals two. The proof derives U(k+t)=2^t throughout 0<=t<=k-1 and combines divisibility of the gcd into the first value two with the exact parity theorem."))), DescribeRole.Theorem))));
}
