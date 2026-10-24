using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangConjecture;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both coefficient assertions of Karp and Zhang's Conjecture 5.2.",
        H("Coefficientwise log-concavity of both series"), Blocks(
            Describe.Lean(DescribeId.Create("karp-zhang-conjecture-five-two-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangConjecture/Result.claim"),
                H("Conjecture 5.2"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Karp and Zhang, Conjecture 5.2, page 12: Suppose that {yₖ}ₖ₌₀∞ is a log-concave sequence. Then the functions μ→ỹ(μ;x) and μ→ŷ(μ;x) are coefficient-wise log-concave on μ>0.")),
                    Paragraph(Text("The real sequence y satisfies KarpZhangReciprocal.Result.IsLogConcave: its terms are nonnegative, it is nontrivial, its adjacent log-concavity inequalities hold, and its support is an interval of integers with the precise zero condition of Definition 1.1. For every positive real mu, nonnegative real alpha and beta, and natural m, claim asserts both 0 at most KarpZhangReciprocal.Result.delta(y,mu,alpha,beta,m) and 0 at most KarpZhangGamma.Series.gammaDelta(y,mu,alpha,beta,m).")),
                    Paragraph(Text("The reciprocal series has coefficient y(k)(2mu) rising factorial k divided by (mu) rising factorial k times k factorial. The gamma series has coefficient y(k)Real.Gamma(mu+k) divided by Real.Gamma(2mu+k) times k factorial. In both cases the Turanian is the product at mu+alpha and mu+beta minus the product at mu and mu+alpha+beta. Finite Cauchy coefficients express the assertion without convergence or growth hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-conjecture-five-two-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangConjecture/Result.result"),
                H("Both halves hold for every coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The theorem proves claim by combining KarpZhangReciprocal.Result.reciprocal_half and KarpZhangGamma.Series.gamma_half with the same sequence, base parameter, shifts and coefficient degree.")),
                    Paragraph(Text("For the reciprocal series, reversible birth-and-death rates bound the score variance of an interval convolution by its expected curvature. Concavity along lines of constant parameter sum and symmetry give the symmetric-tail inequalities. Abel summation combines these tails with the increasing balanced products of a log-concave sequence.")),
                    Paragraph(Text("For the gamma series, exponential smoothing preserves balanced coefficient minors. The paired reciprocal-gamma kernel has nonnegative total and at most one change from negative to positive, so increasing nonnegative smoothed weights give nonnegative coefficients of the two-variable transform. A positive diagonal substitution and the gamma duplication identity transfer these inequalities to the literal gamma-series coefficients. Both shifts may be any nonnegative real numbers, including zero."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-zhang-2023-conjecture-5-2"),
                    ResolutionKind.Proved)))));
}
