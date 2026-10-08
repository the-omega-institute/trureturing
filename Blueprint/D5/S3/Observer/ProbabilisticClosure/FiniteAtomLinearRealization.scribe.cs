using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteAtomLinearRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear readouts of finite native tests in a shared-parameter marker source.",
        H("Native tests and finite joint masses"),
        Blocks(
            Fact("normalized-native-successors", "result", "Linear tests and normalized successors", "For every finite component family, task, strictly positive root parameter and component parameters, and strictly positive weights summing to one, the full carrier has exactly four times the component count plus the task terminal count coordinates. Its action-output columns are normalized and nonnegative, and it preserves every native finite-test probability. For every current history, chosen arm and original source, a native step with positive matrix output mass updates the history feature by dividing its joint matrix pushforward by that output mass. This includes zero replies, marker replies and terminal rejection."),
            Fact("full-feature-updates", "full_feature_updates", "Native feature updates", "For every finite component family, task, strictly positive alpha and component parameters, and positive weights summing to one, the concrete full feature follows the normalized joint output-successor matrix for every history, queried arm and source whenever that output has positive matrix mass."),
            Fact("marker-response-measurable", "measurable_marker_response", "Measurable native marker response", "For each arm and natural edge count, its native marker response is a measurable function of the original source."),
            Fact("denominator-positive", "denominator_pos", "Positive posterior denominator", "For alpha and q in the closed unit interval, if alpha is strictly positive then the denominator alpha plus (one minus alpha) times q to the sum of the two parity bits is strictly positive for every parity pair."),
            Fact("full-terminal-row", "full_terminal_row", "Terminal rows agree with terminal execution", "For every component count, task, alpha, parameter family, terminal coordinate and finite test, its fixed test row at that coordinate equals the zero-or-one decision obtained by terminal execution in that coordinate's mode."),
            Fact("full-active-row", "full_active_row", "Active row recursion", "For every component, parity pair, queried arm and output continuation, the active test row is the zero-output successor row weighted by one minus the component marker rate, plus the terminal continuation decision weighted by the marker rate. The output and terminal mode obey the selected task and the selected parity bit."),
            Fact("full-model-probability", "full_model_probability", "Lawful full finite carrier", "For every finite component family and task, with strictly positive alpha, the full carrier has four times the component count plus the terminal count coordinates, every joint output-successor entry is nonnegative, and each action column sums to one across all outputs and successor coordinates."),
            Describe.Lean(
                DescribeId.Create("native-finite-test-realization"),
                DeclarationHandle.Create(Prefix + "native_finite_test_realization"),
                H("Original-history conditional probabilities have fixed linear readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha and every component parameter q lie in the unit interval and be strictly positive. Let the finitely many real component weights be strictly positive and sum to one. Each component generates two complete conditionally independent Markov arms at the same parameter and root. The source law is the finite mixture of these full source laws.")),
                    Paragraph(Text("For every measurable seed space, independent probability seed law, causal policy, finite time, acquired history and measurable seed event having positive joint mass, the history feature is a nonnegative vector with total mass one. Every finite residual test has original-source joint acceptance mass equal to the conditioning-event mass times the feature vector paired with its fixed test row.")),
                    Paragraph(Text("A test may inspect the current mode, query either arm and branch on the newly acquired output, or finish with a Boolean decision. It reads no old seed or archive. Native queries call the original marker response on the next unread arm edge. The retained-root interface preserves the recovered root after stopping; the emitted-root interface exposes it only in the marker output; the raw interface emits the marker alone. Further terminal queries reject without reading the source.")),
                    Paragraph(Text("The full carrier has four active parity coordinates per component and two shared terminal coordinates for the retained-root interface, or one shared terminal coordinate for the other interfaces. Its cardinality is exactly four times the component count plus the terminal count. Every matrix entry is nonnegative, and for each action and source coordinate the sum over all outputs and successor coordinates is one. Its joint output-successor matrices do not depend on the old history, time or seed. Backward finite-test evaluation gives a single fixed linear row. Original acceptance events and matrix rows are defined independently.")),
                    Paragraph(Text("The proof separates the old seed replay fiber from its original all-zero source cylinder. At a fixed root, extending a cylinder either produces the next all-zero cylinder or its marker complement. After a marker, the residual acceptance decision is source-independent. Root-weight transport and finite mixture summation then identify the native event with the linear row."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Fact(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
