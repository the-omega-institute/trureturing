using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum;

internal sealed class ReadoutInstrumentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.";

    private static DocumentBlock Theorem(string id, string declaration, string title, params string[] prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(prose.Select(p => (DocumentBlock)Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded native FIB continuation is represented by a diagonal quantum instrument.",
        H("Native high-window readout instrument"),
        Blocks(
            Paragraph(Text(
                "This module fixes the five initialized native windows in the foundational order "
                + "(0,2,3,5,25), reads one first window, and appends the native high window (the "
                + "label 5 continuation). The source basis is a finite current-state encoding. "
                + "The acquired outcome keeps the first quantity parity together with the actual "
                + "reply; action history, source ancestry and actual tree leaves remain external.")),
            Paragraph(Text(
                "The two sources whose first seam is one are rejected by the high-window guard. "
                + "The rejection is an absorbing output branch and is retained in the total table. "
                + "The matrix family has one Kraus column per source and one output coordinate for "
                + "each of the three live successors plus the absorbing rejection coordinate.")),
            Theorem("native-reply-table", "native_reply_table", "Exact native continuation table",
                "For each of the five source indices, the existing raw reader evaluated on the "
                + "source window followed by high returns the displayed replies 5, rejection, 18, "
                + "26, rejection. This is a direct finite computation from rawTransition and rawOutput; "
                + "it does not introduce a second reader or identify a tree leaf with a window label."),
            Theorem("diagonal-readout-consumer", "diagonal_readout_consumer", "Diagonal branch factorization and hidden joint mass",
                "For every real diagonal source law p, the branch with acquired parity odd and "
                + "rejection has mass p(25), the hidden joint coordinate kappa. The same theorem "
                + "records the diagonal Kraus factorization for that branch, using the complete "
                + "finite family and aggregate column Gram orthogonality. Branch matrices are "
                + "unnormalized; no conditional state is assigned to a zero-mass branch."),
            Theorem("branch-trace-hidden-joint", "branch_trace_is_hidden_joint", "Born trace of the hidden-joint branch",
                "The trace of the concrete branch state on a diagonal input is exactly the real "
                + "mass p(25), embedded in the complex scalars. This is a branch trace identity for "
                + "the stipulated finite instrument, not a claim of physical preparation, coherence "
                + "control, unrestricted CPTP dynamics, or a Fock-space realization."),
            Paragraph(Text(
                "The generic diagonal Kraus theorem supplies completeness, nonnegative weights, "
                + "the channel obtained by summing branches, and the factorization criterion. "
                + "This FIB application consumes those results at one actual continuation and stops "
                + "there: it does not add a generic quantum wrapper, put provenance in the density "
                + "matrix, or transport the result to arbitrary acquired tree histories.")),
            Paragraph(Text(
                "Dependencies: the existing ImmediateWindowStateCapacity reader and the JointLaw "
                + "native continuation semantics, together with the frozen diagonal Kraus factorization.")))));
}
