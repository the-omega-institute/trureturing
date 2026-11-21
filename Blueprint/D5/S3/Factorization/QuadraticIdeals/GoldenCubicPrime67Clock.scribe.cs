using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicPrime67ClockDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime 67 is a certified native clock with least splitting-readout period sixteen.",
        H("The native prime-67 splitting readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-prime67-least-period"),
                DeclarationHandle.Create(Module + "native_67_least_period"),
                H("The native polynomial splitting readout has exact least period sixteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed Lucas residues form a checked sixteen-state cycle. The finite-field root tests "
                    + "give a sixteen-letter word, and each shorter positive shift fails at an explicitly checked "
                    + "position. The two-state word is read from the polynomial, not presumed from the input "
                    + "period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-split-inert-prefix-period"),
                DeclarationHandle.Create(Module + "unbounded_of_split_inert_prefix"),
                H("An isolated initial positive read forces a large least period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive read followed by a long run of negative reads excludes each shorter period. The "
                    + "unbounded version requires that such prefixes are realizable at every length and that each "
                    + "probe is purely periodic; no prime-density theorem is asserted."))),
                DescribeRole.Theorem))));
}
