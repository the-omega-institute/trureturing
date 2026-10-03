using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenPrimePowerOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A golden residue at exact prime depth has exact order at every higher precision.",
        H("Golden Prime-Power Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-prime-power-order"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order"),
                H("Exact order in the golden residue ring"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p and a golden residue whose two coordinates are not both "
                    + "divisible by p, the element 1+p^m u has order p^n modulo p^(m+n) "
                    + "when m is positive and m+2 is at most p*m. A return at an earlier "
                    + "p-power would make both coordinates vanish modulo p, while the "
                    + "binomial expansion gives the return at p^n."))),
                DescribeRole.Theorem))));
}
