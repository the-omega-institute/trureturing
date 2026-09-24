using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ParityMarkedMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual compensated parity pair and path moments have uniform quadratic normalized error.",
        H("Uniform marked moments for compensated parity experiments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-marked-moment"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/ParityMarkedMoment.uniform_marked_moment_bound"),
                H("Uniform second-order normalized moment estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be any nonempty finite carrier of size n. The real parity function "
                        + "chi takes values plus one and minus one and has sum zero. The real "
                        + "compensation function b has sum zero and absolute value at most one. "
                        + "Both complex marking functions u and v, and b itself, vanish on the "
                        + "negative parity class. Delta is the uniform average of the sum of the "
                        + "norms of u and v. Assume delta is at most one sixty-fourth.")),
                    Paragraph(Text(
                        "The forward transition entry is one plus b at the departure state times "
                        + "chi at the arrival state, divided by n. The reverse entry is its transpose. "
                        + "Each edge mark is one plus u at the departure state plus v there times "
                        + "the arrival parity. All compensation factors are retained. In the Lean "
                        + "statement, the reverse Boolean selects the transpose when true, and the "
                        + "path Boolean selects consecutive transitions when true.")),
                    Paragraph(Text(
                        "The pair moment sums products of stationary ordered-pair weights over "
                        + "all functions from Fin s to pairs of states. Each pair weight includes "
                        + "its uniform departure mass. The path moment sums over all functions "
                        + "from Fin (s + 1) to states, multiplies the s consecutive transition "
                        + "weights and marks, and includes one uniform initial mass. Thus adjacent "
                        + "edges share their intermediate state. Empty products give the zero-time "
                        + "moment one.")),
                    Paragraph(Text(
                        "The mean shift A is the average of u plus b times v in the forward "
                        + "direction, and the average of u in the reverse direction. For every "
                        + "natural s and all four experiment-direction choices, the complex norm "
                        + "of the moment multiplied by exp of minus s A, minus one, is at most "
                        + "64 times s times delta squared times exp of 64 times s times delta "
                        + "squared. The theorem includes delta zero and zero edge marks. It places "
                        + "no sign restriction on the real part of A and no upper restriction on s.")),
                    Paragraph(Text(
                        "Finite path expansion identifies the actual path sum with the uniform "
                        + "average of a matrix power applied to the constant vector. The forward "
                        + "coordinates are the mean and parity-weighted mean. The reverse coordinates "
                        + "add the b-weighted mean. Their exact coefficients retain the reverse "
                        + "unit nilpotent entry. After exponential normalization, use the maximum "
                        + "of the first auxiliary norm and four times the second auxiliary norm. "
                        + "The coupled induction bounds the observed coordinate by H to the power "
                        + "s and the auxiliary norm by ten delta times that power, where H is one "
                        + "plus 22 delta squared. Consequently its return into the observed mean "
                        + "is quadratic. The exponential remainder and finite-product expansion "
                        + "are applications of Mathlib. The weighted matrix-path expansion reuses "
                        + "Zayn Blore's PathSum proof; its copyright, full license and immutable "
                        + "source are preserved in the corresponding library note.")),
                    Paragraph(Text(
                        "The source scope is the finite-s analytic input for Parity Hidden Arrow, "
                        + "Sections 17 and 18: the actual transfer formulas in equations (17.13) "
                        + "through (17.17), the normalized moment control needed by (17.23), and "
                        + "the compensated tilted-weight argument in (17.49) through (17.63). "
                        + "Equation (18.11) is a downstream count-law comparison. This theorem "
                        + "establishes the exact finite-s moment bound on the original pair and "
                        + "path sums, with constants independent of the carrier and marking support.")),
                    Paragraph(Text(
                        "Further obligations are multivariate coefficient extraction with "
                        + "Stirling control, adjustable high-count tails, the relative local-count "
                        + "and all-event comparisons, and the exact compensated overlap-weight "
                        + "substitution with its uniform delta estimate and logarithmic conversion. "
                        + "Support recovery and direction separation still require their "
                        + "large-deviation, posterior, minimax and decision-rule arguments. No "
                        + "phase-boundary equality case, varying-amplitude extension, or equivalence "
                        + "of the complete experiments follows here."))),
                DescribeRole.Theorem))));
}
