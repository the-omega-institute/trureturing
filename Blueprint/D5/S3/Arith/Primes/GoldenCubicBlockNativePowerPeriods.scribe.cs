using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockNativePowerPeriodsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden cubic blocks have disjoint prime supports and exact native power periods.",
        H("Golden Cubic Block Native Power Periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-block-native-power-periods"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods"),
                H("Disjoint supports and power periods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let C_j = |L_(3^j)^2 + 1| and B_j = |L_(3^j)^2 + 3|, "
                    + "where L is the golden Lucas sequence. Let pi(m) be the "
                    + "multiplicative order modulo m of the Fibonacci matrix "
                    + "with rows (1, 1) and (1, 0). For positive indices, "
                    + "distinct C blocks have coprime supports, "
                    + "distinct B blocks have coprime supports, and every C block "
                    + "is coprime to every B block. At each positive index j and "
                    + "positive exponents a and b, the Fibonacci matrix periods "
                    + "of C_j^a and B_j^b are respectively 4 times 3^(j+1) "
                    + "times C_j^(a-1) and 2 times 3^(j+1) times B_j^(b-1). "
                    + "The period of their product is 4 times 3^(j+1) times "
                    + "C_j^(a-1) times B_j^(b-1). Prime ranks separate the "
                    + "supports; the original Fibonacci valuations determine "
                    + "local prime-power periods, and CRT combines them."))),
                DescribeRole.Theorem))));
}
