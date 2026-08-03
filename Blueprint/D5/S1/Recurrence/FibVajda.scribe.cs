using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibVajdaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/FibVajda",
            "Vajda's identity relates shifted Fibonacci products over the integers."),
        H("Vajda's Fibonacci Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("vajda-fibonacci-identity"),
                H("Vajda's identity"),
                LeanTheorem(
                    "D5/S1/Recurrence/FibVajda.fib_vajda"),
                LatexStatement.Create(
                    @"$$F_{n+i}F_{n+j} - F_n F_{n+i+j} = (-1)^n F_i F_j$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For natural indices n, i, and j, the difference between the two "
                    + "shifted Fibonacci products F_(n+i)F_(n+j) and F_nF_(n+i+j) equals "
                    + "(-1)^n F_iF_j. All terms are interpreted in the integers.")))))));
}
