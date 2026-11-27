using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeOddPrimeProbesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform native residual probes and arithmetic inputs for the odd-prime image criterion.",
        H("Exact small-prime Frobenius probes and the large-prime character inputs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-small-odd-prime-certificate"),
                DeclarationHandle.Create(Module + "native_small_prime_certificates"),
                H("Actual reductions give the split and nonsplit probes for 7, 11 and 13"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four good-prime actual group counts yield both separable characteristic-polynomial "
                    + "types with exact companion scalar-power lengths: six and eight, five and twelve, or "
                    + "twelve or four and fourteen. This is finite arithmetic, not a full Galois image theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-seventh-prime-trace-nonzero"),
                DeclarationHandle.Create(Module + "native_trace7_nonzero_mod"),
                H("The good-prime seven trace does not vanish modulo any modulus above three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four native residues at seven give traces one, minus three, minus one, and three, "
                    + "whose reductions are nonzero for every modulus above three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-two-imaginary-char-probes"),
                DeclarationHandle.Create(Module + "two_imaginary_characters_at_seven"),
                H("Neither minus one nor minus two is a square at seven"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact finite field exclusions are the quadratic-character arithmetic input at the "
                    + "uniform good prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-j-offset-even-valuations"),
                DeclarationHandle.Create(Module + "native_j_offset_even_valuation"),
                H("The j-offset has even valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The j-invariant minus 1728 is the square of twenty-four times the native Lucas "
                    + "coordinate. Its valuation is twice the corresponding rational valuation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-j-two-valuation"),
                DeclarationHandle.Create(Module + "native_j_two_exact"),
                H("The two-adic valuation of the native j-invariant is exactly six"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Lucas coordinate is even, so the native block is odd. The remaining coefficient 576 "
                    + "is sixty-four times nine."))),
                DescribeRole.Theorem))));
}
