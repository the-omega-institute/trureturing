using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class SuccessorShortestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating Successor Folds and Shortest Carry Paths.",
        H("Alternating Successor Folds and Shortest Carry Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("successorshortest-carry-steps-mass-lower-bound"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/SuccessorShortest.carry_steps_mass_lower_bound"),
                H("A lower bound for every directed carry path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite path of the four directed Fibonacci carry rules, the initial "
                    + "total coefficient mass is at most the final mass plus the path length. "
                    + "An adjacent carry or a carry on two tokens at index zero removes one token; "
                    + "the other two rules preserve the mass. Induction along the path gives the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("successorshortest-successor-erasure-and-shortest"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/SuccessorShortest.successor_erasure_and_shortest"),
                H("Exact bit changes and the shortest successor path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a canonical Zeckendorf row, take the maximal occupied alternating segment "
                    + "starting at zero when the lowest bit is occupied, and starting at one otherwise. "
                    + "Let its length be k; it is zero when both low bits are empty. The successor "
                    + "erases exactly those k bits and inserts exactly one previously empty bit, "
                    + "leaving every other bit unchanged. Its Hamming distance is k plus one, also "
                    + "equal to two plus the old occupied-bit count minus the new count. The minimum "
                    + "number of carry rewrites is k, attained by the alternating fold and bounded "
                    + "below for every allowed path by the decrease in coefficient mass. Adding the "
                    + "initial unit is an input operation and contributes no carry rewrite."))),
                DescribeRole.Theorem))));
}
