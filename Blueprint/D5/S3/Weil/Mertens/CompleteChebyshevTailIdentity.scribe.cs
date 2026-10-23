using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class CompleteChebyshevTailIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual complete Chebyshev tail has exact Euler normalization.",
        H("Complete Chebyshev tail identity from absolute integrability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-chebyshev-tail-identity"),
                DeclarationHandle.Create(Prefix + "complete_chebyshev_tail_identity"),
                H("Every real endpoint, with all prime powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/lay2015mertenssignchanges")),
                Blocks(
                    Paragraph(Text(
                        "Let K(u)=(psi(u)-u)/u^2, with Mathlib's actual Chebyshev psi. "
                        + "Assume K is Lebesgue integrable on (1,infinity). For every real t>=2, "
                        + "integral(K(u),u>t)=psi(t)/t-sum(Lambda(n)/n,0<n<=floorNat(t))"
                        + "+log(t)-1-EulerGamma. The sum is upper inclusive and contains all prime powers.")),
                    Paragraph(Text(
                        "For real s>1, Mathlib's LSeries_eq_mul_integral_of_nonneg and the actual "
                        + "von Mangoldt logarithmic derivative give "
                        + "-Re(zeta'(s)/zeta(s))=s/(s-1)+s*integral(K(u)*u^(1-s),u>1). "
                        + "Chebyshev's existing linear bound supplies the partial-sum growth "
                        + "hypothesis; SumCoeff owns summability and the interchange. The two "
                        + "real integrands are separately integrable: the damped error is bounded "
                        + "in norm by |K| and u^(-s) is integrable.")),
                    Paragraph(Text(
                        "Dominated convergence sends the damped integral to integral(K,u>1) "
                        + "as s tends to 1 from above. Harmonic.ZetaAsymp already proves the actual "
                        + "Laurent constant: the entire normalized zeta factor has value 1 and "
                        + "derivative EulerGamma at 1. Its continuous logarithmic derivative gives "
                        + "Re(zeta'/zeta)+1/(s-1) tending to EulerGamma. These limits force "
                        + "integral(K,u>1)=-1-EulerGamma. Residue 1 alone is never used to infer "
                        + "the finite part, and the totalized value zeta(1) is not substituted.")),
                    Paragraph(Text(
                        "Apply the existing real-endpoint Abel summation theorem to Lambda and "
                        + "the reciprocal function. It gives integral(K,1..t)="
                        + "sum(Lambda(n)/n,0<n<=floorNat(t))-psi(t)/t-log(t). Splitting the "
                        + "absolutely integrable tail at the same t proves the stated formula. "
                        + "No endpoint avoids integers or prime powers.")),
                    Paragraph(Text(
                        "The transient consumer supplies the old frozen CompleteMertensPeak.hLay "
                        + "argument from this identity. It reuses the existing Johnston-Yang "
                        + "integrability proof on (2,infinity), with only a proposed visibility "
                        + "change, and extends across (1,2) where psi=0. The public frozen peak "
                        + "theorem and its finite kernel ledger stay unchanged. The application "
                        + "still assumes the all-real Johnston-Yang bound and an actual peak; "
                        + "it supplies neither that peak nor an unconditional Robin or RH proof.")),
                    Paragraph(Text(
                        "This packet contains implementation source only. Elaboration, kernel "
                        + "acceptance, the proposed content classification, registration, Scribe "
                        + "validation and freezing are reserved for the later guarded native handoff."))),
                DescribeRole.Theorem))));
}
