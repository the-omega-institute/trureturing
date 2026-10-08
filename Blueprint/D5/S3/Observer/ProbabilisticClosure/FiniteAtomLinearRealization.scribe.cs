using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteAtomLinearRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear readouts of finite native tests in a shared-parameter marker source.",
        H("Native tests and finite joint masses"),
        Blocks(
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
                    Paragraph(Text("The full carrier has four active parity coordinates per component and two shared terminal coordinates for the retained-root interface, or one shared terminal coordinate for the other interfaces. Its joint output-successor matrices do not depend on the old history, time or seed. Backward finite-test evaluation gives a single fixed linear row. Original acceptance events and matrix rows are defined independently.")),
                    Paragraph(Text("The proof separates the old seed replay fiber from its original all-zero source cylinder. At a fixed root, extending a cylinder either produces the next all-zero cylinder or its marker complement. After a marker, the residual acceptance decision is source-independent. Root-weight transport and finite mixture summation then identify the native event with the linear row."))),
                DescribeRole.Theorem))));
}
