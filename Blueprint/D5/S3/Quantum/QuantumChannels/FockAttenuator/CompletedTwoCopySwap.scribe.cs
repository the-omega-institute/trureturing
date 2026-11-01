using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;
internal sealed class CompletedTwoCopySwapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completed Fock tensor coordinates for the actual retained-mode swap.",
        H("Completed two-copy swap coordinates"), Blocks(
            Paragraph(Text("Let H be complex l2(N) and H2=l2(N,H), in the published beam-splitter convention. The occupation pairs are orthonormal and total: testing against a pair reads one actual matrix coefficient. Transporting the completed tensor Hilbert basis through this Fock basis identifies the completion of H tensor H with H2 and sends every pure tensor x tensor y to the published tensor x y: both representations have coefficient x_m y_n. The four-mode proof uses the tensor Hilbert basis of H2 directly. The one-mode occupation basis enters the Gram proof.")),
            Paragraph(Text("For arbitrary completed w in H2, the column square sum is norm(w)^2. HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns constructs C with C e_n=w_n, including every infinite-support slice. Applying C to the occupation-basis expansion of C* x gives the absolutely convergent series inner(w_n,x) w_n, exactly the published purePartialTrace. Thus C C* is the actual reduced operator, positive and trace class by the existing Hilbert-Schmidt product and star-order suppliers.")),
            Theorem("coefficient_mul_adjoint", "The actual coefficient operator",
                "The column synthesis and occupation-basis expansion identify C C* with the existing completed partial trace; no prescribed spectrum or purity premise enters."),
            Theorem("partial_trace_positive_traceClass", "Positivity and trace class",
                "Apply the existing Hilbert-Schmidt product theorem and mul_star_self_nonneg to that equality. The trace-square argument uses these identities."),
            Paragraph(Text("The trace of C C* in any Hilbert basis is the square sum of C* on that basis. The existing Hilbert-Schmidt adjoint identity equates it to the column square sum, so Tr(purePartialTrace w)=norm(w)^2. For w=beamSplitter(1/2)(tensor(a,e2)), the published unitary preserves the norm and the tensor square norm is norm(a)^2 norm(e2)^2=norm(a)^2. Therefore the actual reduced output has trace norm(a)^2 for every complex l2 input, including zero. This direct normalization argument is an application of the cited synthesis and trace suppliers.")),
            Theorem("rotated_environment_expansion", "Exact two-copy environment",
                "The published balanced Fock expansion of e2 tensor e2 has amplitudes sqrt(6)/4 at (4,0) and (0,4), and -1/2 at (2,2), in the original phase convention. Odd difference occupations cancel. Their squared moduli are 3/8,1/4,3/8; these actual coefficients enter the completed difference-swap row sum directly."),
            Paragraph(Text("The same expansion gives the reduced environment (3/8)|e0><e0|+(1/4)|e2><e2|+(3/8)|e4><e4|: substitute its three nonzero slices into the norm-convergent rank-one mixture. Writing this marginal as A, the positive difference (3/8)I-A has quadratic form (3/8)norm(x)^2-(3/8)|x0|^2-(1/4)|x2|^2-(3/8)|x4|^2>=0 by the finite-coordinate Bessel bound. Every other coordinate remains in norm(x). This calculation supports the readable environment argument; the physical compression proof consumes the exact amplitudes directly.")),
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
                H("Completed swap compression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary completed v, evaluate the difference-swap expectation of v tensor the actual rotated environment in the product Hilbert basis. The environment row sum is its diagonal weight at the difference occupation times the squared input coefficient. Every weight is at most 3/8. Absolute convergence follows from the Hilbert-space inner-product series; the full Parseval sum is norm(v)^2. Thus the expectation is at most (3/8)norm(v)^2, retaining every input-center coordinate and every infinite tail."))), DescribeRole.Theorem),
            Theorem("balanced_swap_conjugation", "Conjugate the actual retained swap",
                "Compare the two bounded four-mode maps on coherent product vectors, whose linear span is dense. The exact balanced rotation turns the retained output swap into the exchange of the input and environment difference modes. This equality holds on the completed space and has no support or energy premise."),
            Theorem("retained_swap_gram", "Absolutely convergent Gram square series",
                "The retained-swap expectation of w tensor w is the double sum of squared absolute inner products of its discarded-mode slices. The product Hilbert basis gives an absolutely convergent inner-product series; its reindexing groups the two environment occupations. This includes every completed slice."),
            Theorem("partial_trace_square_swap", "Trace-square equals the actual swap expectation",
                "Let C be the Hilbert-Schmidt operator with actual columns w_n. The existing partial trace is C C*. Trace cyclicity identifies the trace of its square with the trace of (C*C)^2. Parseval turns the latter into the same Gram square series as the actual retained swap. No finite-rank hypothesis enters."),
            Theorem("balanced_fock_two_purity", "All-input balanced Fock-two purity",
                "For arbitrary complex l2 input a, form the actual completed output by applying the published balanced beam splitter to a tensor |2>. The trace-square/swap identity, unitary conjugation and actual environment compression give Tr(sigma_a^2) <= (3/8)norm(a)^4. The squared norm of the two-copy input is norm(a)^4. The zero vector and arbitrary infinite support are included."),
            Paragraph(Text("Apply the countable trace/purity envelope to the actual nonzero output divided by its trace norm(a)^2. The normalized increasing-triple value is at least 25/864. Rescaling by the cube of the trace, (norm(a)^2)^3=norm(a)^6, gives the original increasing-triple value e3(sigma_a)>=(25/864)norm(a)^6 and the signed gap e3(sigma_a)-norm(a)^6/32>=-norm(a)^6/432; zero input gives equality at zero. These are homogeneous applications of the actual purity theorem and the spectral envelope, not a claim that the abstract optimizer (5/12,5/12,1/6) is physically realizable. The stronger universal nonnegative gap and the all-density entropy conclusion remain open.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-two-copy-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-two-copy-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
