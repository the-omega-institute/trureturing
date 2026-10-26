using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class SpectralMomentEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive trace-class operators and the countable moment envelope.",
        H("Trace-class spectral moment envelope"), Blocks(
            Paragraph(Text("The spectral data retain a full Hilbert basis of the actual positive trace-class operator, its nonnegative eigenvalues, and the original operator eigen-equation. Summability makes the nonzero support countable even when the full kernel is nonseparable. Embed that support into N and extend by zero. No trivial-kernel assumption is imposed and no finite-dimensional finrank replaces infinite spectral data.")),
            Node("spectral_moments", "The actual spectrum and all required moments",
                "The existing full spectral theorem supplies the actual eigenbasis. The trace-class ideal supplies the second and third operator powers. Basis-independent trace evaluation identifies their traces with the corresponding eigenvalue power sums; restriction to the nonzero support and extension by zero preserve those sums exactly. For trace one the result is a countable probability sequence. Its absolutely convergent increasing-triple sum equals the Newton expression in the actual first three operator traces. For every coordinate x of this sequence and every index of the full actual eigenbasis, the result retains e3-1/32=(2x-1)(4x-1)^2/32+(x/2)(3/8-Tr(T^2))+e3(remainder). For a nonzero eigenvalue the remainder erases its encoded coordinate; for a zero eigenvalue it keeps the sequence unchanged. Its triple series remains absolutely convergent. This includes zero eigenspaces even when the nonzero sequence has no unused natural-number slot. Neither maximality of x nor a purity bound enters the identity."),
            Node("trace_class_envelope", "The operator envelope",
                "Apply the countable probability results to this actual spectral sequence. This gives both purity branches, the uniform 25/864 bound for purity at most 3/8, and the exact sufficient threshold (17-5 sqrt(5))/16. The operator purity is the real trace of its actual square. The argument imposes neither a finite support cutoff nor faithfulness nor a chosen physically realizable optimizer."),
            Node("spectral_moments_at_mass", "Actual spectrum at arbitrary positive trace",
                "Divide the actual nonzero eigenvalue sequence by its positive trace t. Its mass becomes exactly one, its second and third power sums divide by t squared and t cubed, and multiplying its increasing-triple sum by t cubed recovers the actual operator Newton functional. The original eigenvalue triple series is absolutely convergent as well. This is a homogeneous statement on the original operator; no artificial spectrum is substituted."),
            Node("trace_class_homogeneous_envelope", "Homogeneous trace and purity consequence",
                "For trace t>0 and actual square trace at most (3/8)t squared, the original third symmetric moment is at least (25/864)t cubed. Its difference from t cubed/32 is at least -t cubed/432. This is the homogeneous form consumed by the actual balanced Fock-two specialization."),
            Paragraph(Text("This join reuses the repository's attributed trace-class and compact spectral suppliers and the new countable probability proof. It is not a completed Fock-two purity proof. The physical specialization requires that further analytic step, and the universal e3 >= norm(a)^6/32 and entropy targets remain separate.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("trace-moment-envelope-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/SpectralMomentEnvelope." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
