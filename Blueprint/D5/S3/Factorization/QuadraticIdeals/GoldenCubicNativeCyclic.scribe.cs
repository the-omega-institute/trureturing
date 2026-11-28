using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeCyclicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native Lucas block defines a canonical cyclic cubic.",
        H("Canonical cyclic field of a Lucas block"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-cubic-polynomial"),
                DeclarationHandle.Create(Module + "native_polynomial_certificate"),
                H("Native Eisenstein and polynomial discriminant certificates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The monic depressed cubic attached to the block has a square polynomial discriminant. "
                    + "Translating the root by one gives an Eisenstein certificate at three, proving irreducibility "
                    + "without a square-times-cube hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-cyclic-splitting-field"),
                DeclarationHandle.Create(Module + "native_cyclic_field"),
                H("The native splitting field is cyclic cubic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square discriminant appears concretely in the other two roots as a rational function of "
                    + "the first. It follows that the splitting field already has degree three and its Galois group "
                    + "is cyclic."))),
                DescribeRole.Theorem))));
}
