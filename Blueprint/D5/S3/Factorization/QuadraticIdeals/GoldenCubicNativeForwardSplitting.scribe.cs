using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeForwardSplittingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An earlier block prime splits in every later cyclic field.",
        H("Forward splitting through the native cubic tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-forward-cubic-reduction"),
                DeclarationHandle.Create(Module + "later_cubic_map_eq"),
                H("Earlier divisibility forces a fixed later polynomial reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The next Lucas coordinate vanishes modulo the earlier prime and stays zero. The canonical "
                    + "polynomial reduces to X times X minus three times X plus three. The three roots are distinct "
                    + "at primes greater than three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-forward-residue-product"),
                DeclarationHandle.Create(Module + "earlier_prime_residue_product"),
                H("The full later residue algebra is the product of three prime fields"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit integral trace lattice supplies a conductor multiplier coprime to the earlier "
                    + "prime. The Kummer-Dedekind quotient and the Chinese Remainder Theorem then identify the "
                    + "actual ring of integers modulo that prime with three copies of its prime field."))),
                DescribeRole.Theorem))));
}
