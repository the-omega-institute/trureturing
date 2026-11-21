using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzLogisticEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact upper Petz weight gives a sharp uniform frequency-count bound for evaluation at zero.",
        H("Exact logistic Petz evaluation"),
        Blocks(
            Paragraph(Text("Write w(t) = π/(cosh(2πt) + 1). Integrals in time use Lebesgue measure on the whole real line.")),
            Describe.Lean(
                DescribeId.Create("petz-log-exponential-correlation"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticEvaluation.correlation"),
                H("The log-exponential correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real frequencies ω indexed by a type ι, the complex matrix C = correlation(ω) has entry Cᵢⱼ equal to the integral over x > 0 of exp(−x) exp(i(ωⱼ − ωᵢ) log(x)/(2π)). The integral averages phase differences under the mean-one exponential law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-logistic-exact-gram-factorization"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticEvaluation.exact_gram_factorization"),
                H("Exact factorization of the logistic Fourier Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite index type ι and real frequency map ω, C is positive semidefinite, every Cᵢᵢ is one, and the integral of w(t) exp(i(ωⱼ − ωᵢ)t) is |Cᵢⱼ|² for every pair of indices. The identity includes coincident frequencies.")),
                    Paragraph(Text("The Gamma integral evaluates the log-exponential correlation. Euler's reflection formula gives its squared modulus as (δ/2)/sinh(δ/2) for frequency difference δ ≠ 0, with value one at δ = 0. The cosine transform of w gives the same expression, and evenness cancels the sine transform."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-logistic-weighted-evaluation"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticEvaluation.weighted_evaluation"),
                H("Evaluation at zero with the exact weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite index type ι, real frequencies ω and complex coefficients a, let f(t) = Σᵢ aᵢ exp(iωᵢt). The density w(t)|f(t)|² is integrable and |f(0)|² is at most the integral of that density times the number of distinct frequencies. Equal frequencies are merged by summing their coefficients. The empty index type gives zero on both sides.")),
                    Paragraph(Text("A Gram factorization of C gives unit vectors. The squared Frobenius norm of the sum of their rank-one outer products weighted by aᵢ is the logistic energy. Its trace is Σᵢ aᵢ, so the trace Cauchy–Schwarz inequality gives the count bound. This is the correlation-matrix case of Vybíral’s Schur product inequality (DOI 10.1016/j.aim.2020.107140)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-logistic-uniform-sharpness"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticEvaluation.card_le_of_uniform_bound"),
                H("The least coefficient uniform in the frequencies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let m be a positive natural number. If a real K satisfies |f(0)|² ≤ K times the integral of w(t)|f(t)|² for every injective real frequency list on Fin m and every complex coefficient list on Fin m, then m ≤ K. The evaluation bound holds with K = m for every such list.")),
                    Paragraph(Text("Take all coefficients equal to one and frequencies ωᵢ = iR for R > 0. The off-diagonal Fourier Gram entries tend to zero as R tends to infinity by the Riemann–Lebesgue lemma, while the diagonal stays one. The energy therefore tends to m and the squared evaluation is m²."))),
                DescribeRole.Theorem))));
}
