using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteMertensLedgerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/CompleteMertensLedger.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete Chebyshev tail gives an exact weighted Mertens identity.",
        H("Complete weighted Mertens ledger"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-mertens-ledger"),
                DeclarationHandle.Create(Prefix + "complete_mertens_ledger"),
                H("The complete weighted identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Weil/johnstonyang2022pnt"),
                    LibraryNoteRef.Create("D5/L/Analytic/lay2015mertenssignchanges")),
                Blocks(
                    Paragraph(Text(
                        "For t>=2 let f(u)=(psi(u)-u)/u^2, Q(t)=integral over u>t of f(u), "
                        + "r(u)=(1+log(u))/log(u)^2, and I(t)=integral over u>t of f(u)*r(u). "
                        + "Assume the Johnston–Yang bound |psi(u)-u|<=9.39*u*log(u)^1.515*"
                        + "exp(-0.8274*sqrt(log(u))) for u>=2 and Lay's identity "
                        + "Q(t)=psi(t)/t-(sum of Lambda(n)/n over 0<n<=floor(t))+log(t)-1-gamma. "
                        + "Both f and f*r are absolutely integrable on u>t, and "
                        + "Mertens.E₂Λ(t)=(psi(t)-t)/(t*log(t))-I(t).")),
                    Paragraph(Text(
                        "The two literature statements are hypotheses. The first is Theorem 1.1, "
                        + "equation (1.3), in Johnston–Yang, arXiv:2204.01980v2. The second is the "
                        + "unnumbered complete-prime-power identity in the proof of Lay's Lemma 4, "
                        + "arXiv:1505.03589v1. The resulting weighted identity is derived here.")),
                    Paragraph(Text(
                        "Logarithmic change of variables reduces absolute convergence to the "
                        + "integrability of a real power times an exponential of minus a square root. "
                        + "Fubini applied to the triangle t<s<u proves "
                        + "integral Q(s)/(s*log(s)^2)=Q(t)/log(t)-integral f(u)/log(u). "
                        + "Substitution into the existing complete Mertens formula cancels the "
                        + "Euler constant and gives the stated identity, without differentiating psi "
                        + "at prime powers."))),
                DescribeRole.Theorem))));
}
