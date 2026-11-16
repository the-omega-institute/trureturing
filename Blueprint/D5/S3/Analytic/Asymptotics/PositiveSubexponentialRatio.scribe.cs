using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PositiveSubexponentialRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The magnitude and continuous real-tail phase of an exponential ratio determine its linear term.", H("Positive ratios eliminate a linear exponent"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-subexponential-ratio-linear-exponent-eq-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio.linear_exponent_eq_zero"),
                H("The linear complex exponent vanishes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a,b be arbitrary complex numbers and p,q real functions eventually strictly positive on the full real tail. If log(p(x))/x and log(q(x))/x tend to zero, and exp(a*x+b)*p(x)/q(x) tends to one as real x tends to positive infinity, then a=0. Taking the logarithm of the norm forces the real part to vanish. Translation invariance of the normalized phase limit, followed by a half-turn contradiction, forces the imaginary part to vanish. This result is consumed by SparseQuartetProduct.fast_ratio_rigidity."))), DescribeRole.Theorem),
            Paragraph(Text("The conclusion concerns a, not the chosen logarithm b. It uses eventual positivity and a full real-tail limit, not integer samples. It makes no actual-zeta, RH, minimal-type or literature-novelty claim. This is a general asymptotic theorem, not enumeration, numerical reduction, checker infrastructure or a certified finite instance; utility is none. The proof uses Mathlib logarithm, exponential, limit and trigonometric identities.")))));
}
