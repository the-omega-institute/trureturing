using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class NormalizedQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual normalized quotient observation", H("Actual normalized quotient observation"), Blocks(
            Paragraph(Text("The actual monic quotient Z[X]/(f) is Mathlib AdjoinRoot of the characteristic polynomial. LinearRecurrence coefficients are ascending: manuscript c_j is coeffs(k-j). The source equation L(x^n)=U_n is proved through the canonical remainder coefficient, the quotient root relation and uniqueness of the actual impulse recurrence. The triangular block/nonconstant-coordinate ideal correspondence is supplied by QuotientBlock; for order at least two, QuotientBlock also proves a positive scalar-return block rank at every prime not dividing the characteristic polynomial constant coefficient; general-modulus scalar returns and valuation lifting remain open; this theorem does not assume those conclusions as parameters. The observation_eq_impulse registration is declared_validated in the current scoped report; this does not certify other family targets.")),
            Describe.Lean(DescribeId.Create("normalizedquotient-observation-eq-impulse"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/NormalizedQuotient.observation_eq_impulse"),
                H("observation_eq_impulse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/jaidee2026blockdold")),
                Blocks(Paragraph(Text("For every integer LinearRecurrence E with positive order and every natural n, taking coefficient E.order-1 of the canonical monic remainder of the nth power of the quotient root equals the actual impulse solution E.mkSol with initial values 0,...,0,1. Neither irreducibility nor a nonzero trailing coefficient is needed for this observation identity. To use the complete block theorem one still needs order at least two, nonzero trailing coefficient, positive block gcd and primes not dividing that coefficient."))), DescribeRole.Theorem))));
}
