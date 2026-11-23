using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeResidueIncompatibilityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeResidueIncompatibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native mod-13 and mod-73 patterns cannot simultaneously split.",
        H("Incompatible residue observations at 13 and 73"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-clock-incompatible-cubic-roots"),
                DeclarationHandle.Create(Module + "no_native_simultaneous_polynomial_roots"),
                H("The two polynomial reductions never have roots simultaneously"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual Lucas recurrence binds every native level to two checked finite residue cycles. "
                    + "The times giving roots over the two prime fields are disjoint within their common phase "
                    + "modulus."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-clock-incompatible-residue-maps"),
                DeclarationHandle.Create(Module + "no_native_pair_of_residue_maps"),
                H("No native ring of integers has both prime-field residue maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An integral canonical root would reduce under each proposed ring map. The two resulting "
                    + "finite-field roots contradict the native clock incompatibility. This theorem neither "
                    + "excludes a square-times-cube block nor classifies all Frobenius phases."))),
                DescribeRole.Theorem))));
}
