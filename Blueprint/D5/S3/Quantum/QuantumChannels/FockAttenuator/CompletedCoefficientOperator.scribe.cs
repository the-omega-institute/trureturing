using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;
internal sealed class CompletedCoefficientOperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual coefficient operator and reduced state on completed two-mode Fock space.",
        H("Completed coefficient operator"), Blocks(
            Paragraph(Text("Let H be complex l2(N) and H2=l2(N,H), in the existing beam-splitter convention where the nth discarded-mode slice is a vector of H. For arbitrary w in H2, the column square sum is norm(w)^2. The existing Hilbert-Schmidt column synthesis supplier therefore constructs C with C e_n = w_n. This uses the actual completed vector and all its infinitely many columns.")),
            Node("coefficient_mul_adjoint", "Equality with the existing reduced operator",
                "Apply C to the occupation-basis expansion of C* x. Adjoint duality turns the resulting summands into inner(w_n,x) w_n. Their sum is exactly the existing partial trace mixture, so C C* equals that actual operator."),
            Node("partial_trace_positive_traceClass", "Positivity and trace class",
                "The Hilbert-Schmidt product theorem gives trace class for C C*, and the star-algebra order gives positivity. These properties belong to the actual partial trace just identified."),
            Node("partial_trace_trace", "Exact trace normalization",
                "The trace of C C* in any Hilbert basis is the square sum of C* on that basis. The existing basis-independent Hilbert-Schmidt adjoint identity identifies it with the column square sum, hence with norm(w)^2."),
            Node("balanced_fock_two_normalization", "Actual balanced two-photon specialization",
                "Take w = beamSplitter(1/2)(tensor(a,e2)) using the published completed beam unitary. Its norm squared is norm(a)^2 for every complex l2 input, including zero. The selected coefficient operator is Hilbert-Schmidt, its product with its adjoint is the actual reduced operator, and that operator has trace norm(a)^2."),
            Paragraph(Text("The column construction reuses HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns and the attributed trace-class suppliers. This module does not establish the all-input purity estimate 3/8. That estimate requires the completed two-copy retained-swap compression, including its exact environment marginal; it cannot be inferred from normalization or from an arbitrarily prescribed spectrum.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("completed-coefficient-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedCoefficientOperator." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
