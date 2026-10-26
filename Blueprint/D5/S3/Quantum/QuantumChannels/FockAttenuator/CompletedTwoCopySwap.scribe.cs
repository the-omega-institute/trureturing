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
            Node("centerDifference", "Actual center and difference rotation",
                "Regroup the four completed modes and apply the inverse balanced beam rotation to both pairs. The completed tensor map preserves inner products and norms."),
            Describe.Lean(DescribeId.Create("completed-two-copy-compression"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap.difference_swap_compression"),
                H("Completed swap compression"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary completed v, evaluate the difference-swap expectation of v tensor the actual rotated environment in the product Hilbert basis. The environment row sum is its diagonal weight at the difference occupation times the squared input coefficient. Every weight is at most 3/8. Absolute convergence follows from the Hilbert-space inner-product series; the full Parseval sum is norm(v)^2. Thus the expectation is at most (3/8)norm(v)^2, retaining every input-center coordinate and every infinite tail."))), DescribeRole.Theorem),
            Theorem("balanced_swap_conjugation", "Conjugate the actual retained swap",
                "Compare the two bounded four-mode maps on coherent product vectors, whose linear span is dense. The exact balanced rotation turns the retained output swap into the exchange of the input and environment difference modes. This equality holds on the completed space and has no support or energy premise."),
            Theorem("retained_swap_gram", "Absolutely convergent Gram square series",
                "The retained-swap expectation of w tensor w is the double sum of squared absolute inner products of its discarded-mode slices. The product Hilbert basis gives an absolutely convergent inner-product series; its reindexing groups the two environment occupations. This includes every completed slice."),
            Theorem("partial_trace_square_swap", "Trace-square equals the actual swap expectation",
                "Let C be the Hilbert-Schmidt operator with actual columns w_n. The existing partial trace is C C*. Trace cyclicity identifies the trace of its square with the trace of (C*C)^2. Parseval turns the latter into the same Gram square series as the actual retained swap. No finite-rank hypothesis enters."),
            Theorem("balanced_fock_two_purity", "All-input balanced Fock-two purity",
                "For arbitrary complex l2 input a, form the actual completed output by applying the published balanced beam splitter to a tensor |2>. The trace-square/swap identity, unitary conjugation and actual environment compression give Tr(sigma_a^2) <= (3/8)norm(a)^4. The two-copy input norm is norm(a)^4. The zero vector and arbitrary infinite support are included."),
            Paragraph(Text("Apply the countable trace/purity envelope to the actual nonzero output divided by its trace norm(a)^2. The resulting increasing-triple value is at least (25/864)norm(a)^6, and its gap from norm(a)^6/32 is at least -norm(a)^6/432; zero input gives equality at zero. These are homogeneous applications of the actual purity theorem and the spectral envelope, not a claim that the abstract optimizer (5/12,5/12,1/6) is physically realizable. The stronger universal nonnegative gap and the all-density entropy conclusion remain open.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-two-copy-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-two-copy-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
