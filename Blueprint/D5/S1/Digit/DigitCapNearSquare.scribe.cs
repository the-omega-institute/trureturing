using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapNearSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapNearSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/dumont1999linearrecurrent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The digit cap ell^2−2 has upper growth exponent log_ell λ with λ^2=(ell−1)(λ+1), "
            + "and this exponent is below 1.",
        H("The digit cap ell^2 − 2"),
        Blocks(
            Describe.Lean(DescribeId.Create("digit-cap-near-square-root"),
                DeclarationHandle.Create(Prefix + "lam"),
                H("The dominant root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "lam ell is (ell−1+√(ell^2+2ell−3))/2, the positive root of "
                    + "λ^2=(ell−1)(λ+1). For ell≥2 it satisfies 1≤λ<ell."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("digit-cap-near-square-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exponent of the cap ell^2 − 2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural ell≥2, the extended-real upper exponent of the digit cap "
                    + "ell^2−2 at radix ell equals log_ell(lam ell), and log_ell(lam ell)<1. "
                    + "This is Proposition 6.9 of Dumont, Sidorov and Thomas for the alphabet "
                    + "of size ell^2−1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("digit-cap-near-square-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Proof by window envelopes and alternating digits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write b(n) for the count with digits at most ell^2−2. The lowest-digit "
                    + "recursion gives b(ell·q+r)=b(q)+…+b(q−ell+1) for r≤ell−2 and the same "
                    + "sum with ell−1 terms for r=ell−1. Among ell consecutive window terms at "
                    + "most one has last digit ell−1, and the remaining terms number at most "
                    + "ell−1. So the largest full and short windows below ell^(m+1) are at most "
                    + "(ell−1)X+Y and (ell−1)X, where X and Y bound them below ell^m. These "
                    + "envelopes satisfy x(m+2)=(ell−1)(x(m+1)+x(m)), so b(n)≤ell·b(0)·λ^m for "
                    + "n<ell^(m+1), and the readout at n≥2 is at most log_ell λ+log(ell·b(0))/log n. "
                    + "For the lower bound let the quotient digits alternate ell−2, ell−1 above a "
                    + "leading 1. The full window v(k) at the k-th quotient then satisfies "
                    + "v(k+2)=(ell−1)(v(k+1)+v(k)) exactly, so λ·v(k)≥λ^k, and at "
                    + "n=ell·q(k)<ell^(k+2) the readout is at least log_ell λ·(k−1)/(k+2). "
                    + "Every tail supremum is therefore at least log_ell λ and eventually at most "
                    + "log_ell λ plus any positive ε, so the exponent is log_ell λ. Finally "
                    + "√(ell^2+2ell−3)<ell+1 gives λ<ell, so the exponent is below 1."))),
                DescribeRole.Theorem))));
}
