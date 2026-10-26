using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;
internal sealed class CompletedTwoCopySwapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completed Fock tensor coordinates for the actual retained-mode swap.",
        H("Completed two-copy swap coordinates"), Blocks(
            Paragraph(Text("The one-mode space is complex l2(N). The published two-mode space is nested l2(N,l2(N)). Its occupation pairs are an orthonormal and total family: testing against each pair reads one actual matrix coefficient. The resulting Hilbert basis identifies the completion of H tensor H with this nested space and maps every pure tensor to the published tensor vector.")),
            Node("completedPair", "Actual two-mode identification",
                "Transport the completed product Hilbert basis to the nested-l2 Fock basis. This is a unitary identification on the entire Hilbert space, with arbitrary infinite-support inputs."),
            Node("retainedSwap", "The bounded retained-mode exchange",
                "On the completed tensor of two two-mode spaces, permute only the two retained occupation indices. The environment indices stay in their original positions. Hilbert-basis coordinate transport makes this an actual bounded unitary."),
            Node("regroup", "Input and environment regrouping",
                "The middle-index permutation sends (input1,environment1),(input2,environment2) to (input1,input2),(environment1,environment2). On every completed product vector this agrees with the actual tensor regrouping."),
            Node("differenceSwap", "Difference-mode exchange",
                "After the center/difference rotation, exchange only the input and environment difference indices. All center coordinates and all Hilbert-space tails remain in the definition."),
            Describe.Lean(DescribeId.Create("completed-two-copy-compression"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap.difference_swap_compression"),
                H("Completed swap compression"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary completed v, evaluate the difference-swap expectation of v tensor the actual rotated environment in the product Hilbert basis. The environment row sum is its diagonal weight at the difference occupation times the squared input coefficient. Every weight is at most 3/8. Absolute convergence follows from the Hilbert-space inner-product series; the full Parseval sum is norm(v)^2. Thus the expectation is at most (3/8)norm(v)^2, retaining every input-center coordinate and every infinite tail."))), DescribeRole.Theorem),
            Paragraph(Text("These coordinates are a supporting construction. The source candidate still requires the bounded-map conjugation identity and the trace-square/retained-swap identity before it can prove the all-input balanced Fock-two purity estimate. No full purity or entropy conclusion follows from the coordinate definitions alone.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-two-copy-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
