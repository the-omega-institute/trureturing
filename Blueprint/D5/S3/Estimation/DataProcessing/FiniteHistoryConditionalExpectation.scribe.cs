using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FiniteHistoryConditionalExpectationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive finite-history likelihoods determine a normalized joint law and conditional expectations on recorded prefixes.",
        H("Conditional Expectation on Finite Observation Histories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-history-conditional-expectation"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.history_law_conditional_expectation"),
                H("The joint law and recorded-prefix conditioning"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be a finite hidden-state space and let Z(n) be the finite "
                        + "alphabet of the next observation at time n. Fix any natural-number "
                        + "horizon N, including zero. A normalized nonnegative prior nu on J "
                        + "and normalized nonnegative kernels K(n,j,h) are given for n below N. "
                        + "Each kernel may depend on the fixed hidden state j and the complete "
                        + "recorded history h. Zero prior coordinates and zero kernel entries "
                        + "are permitted. All subsets of these finite spaces are measurable.")),
                    Paragraph(Text(
                        "The likelihood L(empty,j) is one. Appending observation z multiplies "
                        + "L(h,j) by K(n,j,h,z). The measure on pairs (j,w), with w a complete "
                        + "record, assigns mass nu(j) times L(w,j) to each point. This measure "
                        + "is a probability measure. For every time t at most N and every "
                        + "real test function F(j,h), its integral at the hidden state and "
                        + "recorded prefix equals the finite sum of nu(j) times L(h,j) times "
                        + "F(j,h). In particular, the joint mass of hidden state j and prefix "
                        + "h is nu(j) times L(h,j).")),
                    Paragraph(Text(
                        "Write P(h) for the sum of nu(j) times L(h,j) over hidden states. "
                        + "For each t below N and every real function f of a length-(t+1) "
                        + "record, the conditional expectation of f at the next prefix, "
                        + "given only the current recorded prefix h, is the sum over z of "
                        + "P(hz) divided by P(h), multiplied by f(hz). The equality holds "
                        + "almost everywhere under the joint law. The sigma-algebras of "
                        + "recorded prefixes form a filtration; its generators omit the "
                        + "hidden-state coordinate.")),
                    Paragraph(Text(
                        "If a history has zero mass, nonnegativity and normalization force "
                        + "every child history to have zero mass. The displayed scalar formula "
                        + "is then zero under totalized real division. It does not assign a "
                        + "conditional probability distribution to a null history.")),
                    Paragraph(Text(
                        "The proof removes the last observation by induction, preserving "
                        + "every earlier prefix test function. The resulting marginal identity "
                        + "normalizes the joint law. Equality of integrals on every recorded-prefix "
                        + "cylinder then identifies the conditional expectation. Posterior "
                        + "relative-entropy balances and their compensated martingales require "
                        + "additional identifications beyond this probability-law theorem."))),
                DescribeRole.Theorem))));
}
