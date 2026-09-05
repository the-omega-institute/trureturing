using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4DenseInputDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/GoldenBase4DenseInput.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing M01 dense input has its exact arithmetic value and a legal run, connecting the interval machine to every required base-four power digit.",
        H("Canonical Input Transport for the Golden Base-Four Machine"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-1"),
                DeclarationHandle.Create(Prefix + "occupied_index_bounds"),
                H("Occupied indices fit the existing display length"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Upstream canonicality gives indices at least two and a decreasing gap of at least two. The head index used by M01 bounds every occupied index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-2"),
                DeclarationHandle.Create(Prefix + "dense_fibonacci_value"),
                H("Dense displays have their standard weighted values"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction over display width relates the existing interval-machine value to a finite sum of Nat.fib weights. This lemma is valid for any bit family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-3"),
                DeclarationHandle.Create(Prefix + "zeckendorfMSDWord_value"),
                H("The M01 input word evaluates exactly to its argument"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index shift i maps to i+2 is a finite bijection from the selected display positions to the upstream occupied indices. Their Fibonacci sum is n by decode_wdigits. Neither the encoder nor its mathematical value is assumed as an extra premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-4"),
                DeclarationHandle.Create(Prefix + "separated_bits_run"),
                H("Separated bits admit legal runs of the shared base"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A previous-one entry requires the next displayed bit to be zero. The guarded induction proves legality without silently resetting the previous-bit type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-5"),
                DeclarationHandle.Create(Prefix + "zeckendorfMSDWord_legal"),
                H("The M01 word is accepted by the existing Zeckendorf base"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonconsecutive occupied Fibonacci indices yield separated dense bits. The shared two-type base therefore accepts every M01 word, including the one-zero display of zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-6"),
                DeclarationHandle.Create(Prefix + "base4PowerWord_correct"),
                H("The explicit machine computes the original M01 digit on every power"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proved dense-word value and legality feed the interval invariant. Exact cast and power identities identify its floor difference with base4DigitInt and its output with base4GoldenDigit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base-four-dense-7"),
                DeclarationHandle.Create(Prefix + "twenty_one_state_power_witness"),
                H("A twenty-one-state witness satisfies the exact power task"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness uses Fin 21 and the original M01 power-word and digit functions, together with the zero self-loop and zero initial output. This theorem has no finite-sample or caller-supplied correctness premise. It states an upper construction, not a minimum-state lower bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenBase4IntervalMachine")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenBase4AutomataOracle"))
        ]));
}
