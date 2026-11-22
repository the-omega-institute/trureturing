using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class NativePastAcquisitionBarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/NativePastAcquisitionBarrier.";
    private static Formula N => F.Id("n");
    private static Formula Vn => new Formula.Subscript(F.Id("v"), N);
    private static Formula Thresholds => Seq(
        F.Id("n"), Ge, Sp, D(2), Comma, Sp,
        Vn, Eq, new Formula.Subscript(F.Id("F"), N), Minus, D(1), Quad, Sp,
        Vn, Lt, Sp, D(2), F.Id("d"), Comma, Quad, Sp,
        Vn, Lt, Sp, D(2), F.Id("K"), Minus, D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the native serial service, finite past acquisition does not expose " +
        "bits newer than the mature word at the final cut.",
        H("Past native acquisition and the update barrier"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-native-past-acquisition-barrier"),
            DeclarationHandle.Create(Prefix + "native_past_acquisition_barrier"),
            H("Exact trace replay and the two class-uniform barriers"),
            StatementSource.FromAuthor(Disp(Thresholds)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two strict inequalities are separate subthreshold conditions: " +
                    "the first for unknown-order Boolean recurrences of public cap d≥0, " +
                    "the second for nonempty autonomous unary Moore sources of cap K≥1. " +
                    "The trace assertion itself holds also at the fixed cuts zero and one.")),
                Paragraph(Text(
                    "A common source-blind observer starts at alpha and makes serial " +
                    "literal Reads, actual Updates with a common acknowledgement, arbitrary " +
                    "source-free local changes and retention, or a local stop. Decisions see " +
                    "only the public input, common independent tape and accessible record. " +
                    "The record retains requested physical addresses, replies, local events, " +
                    "state and retained data. No label snapshot, private source data, " +
                    "physical duration or extra observation is provided.")),
                Paragraph(Text(
                    "Every finite prefix ending no later than a chosen cut is equal to " +
                    "replaying from its mature word with fixed padding, on identical public " +
                    "inputs and tape. The prefix need not be terminal and there is no common " +
                    "bound on local or service steps. For equal mature words, every record " +
                    "event at the fixed cut has the same tape preimage under both sources.")),
                Paragraph(Text(
                    "Below the appropriate threshold, no common observer and answer decoder " +
                    "can stop correctly at the fixed cut eventually under one shared proper " +
                    "tape filter for every lawful source, for any of the three tasks separately: " +
                    "full current labels, all next-cut literal presence replies, or complete " +
                    "finite future behavior. The two task-specific successes would be disjoint " +
                    "tape events but both eventual. This applies in particular to a shared " +
                    "almost-sure tape law. It does not bound paid reads or search work, and " +
                    "does not assert a fixed difficult source or a per-fiber failure."))),
            DescribeRole.Theorem))));
}
