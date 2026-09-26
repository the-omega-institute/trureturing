using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class GoldenCubicBlockCongruencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Congruences and two-adic valuations at the power-of-three golden indices.",
        H("Golden Cubic Block Congruences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-block-residues"),
                DeclarationHandle.Create("D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_lucas_block"),
                H("Lucas residues at cubic block indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive j, the Lucas number at index 3^j is four modulo "
                    + "seventy-two and has two-adic valuation two. Its square plus three is "
                    + "one modulo nine, and its square is one modulo five. The square "
                    + "plus three is nineteen modulo eighty. The next Lucas value "
                    + "is the current value times its square plus three. The residue "
                    + "statements follow from this cubic recurrence and induction on j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-block-residue"),
                DeclarationHandle.Create("D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_fibonacci_block"),
                H("Fibonacci residue at cubic block indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive j, the Fibonacci number at index 3^j is two "
                    + "modulo four and has two-adic valuation one. The next Fibonacci "
                    + "value is the current one times the square of the current Lucas "
                    + "value plus one. Its residue follows from this coordinate identity "
                    + "and the Lucas congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interlevel-block-congruence"),
                DeclarationHandle.Create("D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_interlevel"),
                H("Interlevel cubic block congruence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any positive earlier index i and later index j, the block formed from "
                    + "the Lucas number at 3^i divides the Lucas number at 3^j. "
                    + "Consequently the later block is three modulo the square of "
                    + "the earlier block. The divisibility propagates through the "
                    + "cubic Lucas recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-block-product"),
                DeclarationHandle.Create("D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_product"),
                H("Product of earlier cubic blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Lucas number at index 3^j is four times the product of "
                    + "the blocks formed at all positive earlier indices. The identity "
                    + "starts at the Lucas value four at index three and extends "
                    + "one factor at each cubic recurrence step."))),
                DescribeRole.Theorem))));
}
