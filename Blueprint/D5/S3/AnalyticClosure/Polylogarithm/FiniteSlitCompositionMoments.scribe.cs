using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitCompositionMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual normalized Xu--Zhao reciprocal branches have a finite bank contribution that "
        + "eventually dominates every outer geometric error, for all positive compositions and powers.",
        H("FiniteSlitCompositionMoments"), Blocks(
            Describe.Lean(DescribeId.Create("origin-correct-reciprocal"),
                DeclarationHandle.Create(Prefix + "reciprocal"),
                H("The origin-correct reciprocal branch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For head : PNat, tail : List PNat and ell : PNat, reciprocal is the ell-th "
                    + "power of the inverse of CompositionZeroFreeCollar.normalizedContinuation. "
                    + "At zero it uses CompositionDisk.normalized, preserving the removable "
                    + "source value rather than taking total division in the unnormalized quotient."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("all-composition-bank-domination"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The literal same-power bank integral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text(
                        "For every positive head, every finite positive-entry tail, and every "
                        + "positive reciprocal power ell, there are R0>1, 0<rho<1, "
                        + "1<R<min(R0,1+rho), and an upper bank. The actual reciprocal is analytic "
                        + "on omega intersect norm(z)<R0, agrees with the disk reciprocal on norm(z)<1, "
                        + "and has its correct value at zero. The upper bank is continuous on the "
                        + "closed upper half-collar and agrees there with the reciprocal at every "
                        + "point of omega. At one its value is zeta(head,tail)^(-ell) for head>1 "
                        + "and zero for head=1. There is also a nonnegative constant bounding the norm "
                        + "of the actual reciprocal at every point of omega on the fixed circle of radius R.")),
                    Paragraph(Text(
                        "For every real B, B/R^n plus (1/pi) times the integral from 1 to R of "
                        + "Im upper(x)/x^(n+1) is strictly negative eventually. CompositionBanks.result "
                        + "is used at this same ell, and CompositionZeroFreeCollar.result supplies "
                        + "the actual zero-free radius. The radius R is 1+min(R0-1,rho)/2. "
                        + "The bank density h(x)=-Im upper(x) is continuous, zero at one and "
                        + "strictly positive inside the interval. FiniteSlitBankMoments.bank_dominance "
                        + "then supplies the strict geometric comparison. For the outer norm bound, "
                        + "separate the circle by a distance delta strictly between R-1 and rho from one. "
                        + "Its far part is a compact subset of omega. On the near part, the upper "
                        + "or lower closed half-collar gives the bound according to the sign of Im z.")),
                    Paragraph(Text(
                        "The positive compositions use the original largest strict index and "
                        + "depth(tail)=1+length(tail). Every finite leading-one block and every "
                        + "positive ell is included. No global nonvanishing premise is imposed. "
                        + "The Cauchy coefficient identity and shrinking connector limits remain "
                        + "to be established, together with the geometric bound for the actual "
                        + "outer coefficient integral. Taylor coefficients must also be "
                        + "identified with the exact ordinary formal inverse, followed by the "
                        + "all-j finite-prefix and strict admissible lower-bound argument. "
                        + "Consequently this result does not prove eventual coefficient negativity "
                        + "or resolve Xu--Zhao Conjecture 1.3."))),
                DescribeRole.Theorem))));
}
