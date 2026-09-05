using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4IntervalMachineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/GoldenBase4IntervalMachine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit typed twenty-one-state table follows an exact golden-error invariant on every legal Fibonacci-weighted word.",
        H("Golden Base-Four Interval Machine"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-base-four-machine"),
                DeclarationHandle.Create(Prefix + "machine"),
                H("An explicit typed twenty-one-state machine"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The table uses the existing TypedPartialDFAO and its binary Zeckendorf base. All legal transitions are present; one after one remains undefined. The initial output and zero loop are both zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-base-four-fibPair-append-digit"),
                DeclarationHandle.Create(Prefix + "fibPair_append_digit"),
                H("Fibonacci input evaluation follows an exact recurrence"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two coordinates evaluate the word with Nat.fib weights and its shifted weights. Appending a bit updates the registers to (v+a,q+v+2a). No canonical Zeckendorf encoder is redefined."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-error-append-digit"),
                DeclarationHandle.Create(Prefix + "error_append_digit"),
                H("The error coordinate intertwines arithmetic and transitions"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial identity phi squared equals phi plus one converts the two-register update into e maps to (1-phi)e-a(1-phi) squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-endpoint-certificate"),
                DeclarationHandle.Create(Prefix + "endpoint_certificate"),
                H("Entire interval images fit the table"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each noninitial interval has a noninitial destination. Because the affine slope is negative, the image of the upper endpoint is compared with the destination lower endpoint. These are finite exact algebraic inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-step-preserves-cell"),
                DeclarationHandle.Create(Prefix + "step_preserves_cell"),
                H("The state invariant survives every defined transition"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial singleton is handled separately. No premise about unreachable artificial cut points is needed: interval preservation and the initial invariant already imply that every reached error belongs to its state cell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-cell-output-strip"),
                DeclarationHandle.Create(Prefix + "cell_output_strip"),
                H("A whole cell has one radix-four output"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each cell lies in the half-open digit strip assigned to the output, inside an explicitly specified integer strip."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-cell-floor-values"),
                DeclarationHandle.Create(Prefix + "cell_floor_values"),
                H("The invariant determines two integer floors"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The interval bounds identify floor(e) and floor(4e) exactly, using the upstream integer floor interface."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-cell-digit"),
                DeclarationHandle.Create(Prefix + "cell_digit"),
                H("The represented integer has the emitted digit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracting an integer coordinate does not change the digit. The theorem proves the difference of floors directly from inequalities rather than numerical approximation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-initial-cell"),
                DeclarationHandle.Create(Prefix + "initial_cell"),
                H("The empty input starts at the zero singleton"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial error and initial state satisfy the invariant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-runFrom-cell"),
                DeclarationHandle.Create(Prefix + "runFrom_cell"),
                H("Induction transports the invariant through every successful run"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This induction uses the existing runTransition semantics. It retains the full consumed prefix, relating each new state to the arithmetic value of the appended word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-successful-run-digit"),
                DeclarationHandle.Create(Prefix + "successful_run_digit"),
                H("Every successful run computes the exact floor difference"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement quantifies over words of arbitrary length. No finite regression extent or caller-supplied correctness implication occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-legal-step-exists"),
                DeclarationHandle.Create(Prefix + "legal_step_exists"),
                H("Every permitted base step is implemented"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite table is total on the allowed symbols of each numeration type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-legal-run-exists"),
                DeclarationHandle.Create(Prefix + "legal_run_exists"),
                H("Every legal word has a successful run"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction lifts legal base runs to machine runs. This closes the potential loophole in a theorem conditioned only on successful machine runs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-every-legal-word-correct"),
                DeclarationHandle.Create(Prefix + "every_legal_word_correct"),
                H("All legal Fibonacci-weighted words receive the correct output"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This combines totality on legal words with the invariant. The separate M01 dense-word legality and value bridge is not claimed here; powers-only minimality is also not claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-leading-zero-invariant"),
                DeclarationHandle.Create(Prefix + "leading_zero_invariant"),
                H("Leading zeroes do not affect the output"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof reuses the existing leading-zero theorem with the concrete zero self-loop."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Automata/TypedPartialDFAOOverBase"))]));
}
