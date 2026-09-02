using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyAnnihilatorIdentificationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/"
            + "FinitePronyAnnihilatorIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recurrence valid on a full separated Prony window contains every "
            + "true node and uniquely determines the bounded monic annihilator.",
        H("Finite Prony Annihilator Identification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-recurrence-window-identifies-node-roots"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_recurrence_window_identifies_node_roots"),
                H("A full recurrence window identifies every active Prony node"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For distinct nodes with nonzero weights, a candidate polynomial whose "
                            + "coefficient recurrence vanishes on the first matching number of "
                            + "time shifts must vanish at every true node.")),
                    Paragraph(Text(
                        "The proof converts candidate evaluations into residual modal weights. "
                            + "Their first moment window vanishes, so frozen Vandermonde "
                            + "injectivity forces every residual weight to be zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-recurrence-degree-lower-bound"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_recurrence_degree_lower_bound"),
                H("Every nonzero valid recurrence has degree at least the active mode count"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All true linear factors divide every nonzero candidate satisfying the "
                            + "full recurrence window. Polynomial degree monotonicity under "
                            + "divisibility therefore gives the mode-count lower bound.")),
                    Paragraph(Text(
                        "This establishes exact recurrence-order minimality in the separated "
                            + "active-mode regime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-annihilator-unique-from-window"),
                DeclarationHandle.Create(
                    Prefix + "existsUnique_finite_prony_annihilator_from_window"),
                H("The bounded monic Prony annihilator is unique"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The genuine node annihilator is monic, has degree equal to the number "
                            + "of modes, and satisfies the recurrence window. Any other monic "
                            + "candidate of degree at most that count is divisible by the true "
                            + "annihilator and hence equal to it.")),
                    Paragraph(Text(
                        "The theorem proves structural identifiability. It does not compute the "
                            + "coefficients from floating-point data or control noisy root "
                            + "perturbations."))),
                DescribeRole.Theorem)),
        []));
}
