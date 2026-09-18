using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Powerful;

internal sealed class PowerfulNumberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Powerful/PowerfulNumber.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/golomb1970powerful");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integer in which every prime divisor occurs to order at least two is a "
            + "square times a cube with squarefree cube root.",
        H("Powerful numbers and their square-cube representation"),
        Blocks(
            Paragraph(Text(
                "The powerful condition is stated on prime divisors rather than on exponents, so "
                    + "it reads directly off divisibility. The representation converts it into a "
                    + "shape from which the density of powerful numbers and their appearance in "
                    + "additive questions can be read.")),
            Describe.Lean(
                DescribeId.Create("powerful-definition"),
                DeclarationHandle.Create(Prefix + "Powerful"),
                H("Powerful integers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Powerful n holds when n is nonzero and, for every prime p dividing n, the "
                        + "square of p also divides n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golomb-representation"),
                DeclarationHandle.Create(Prefix + "golomb_representation"),
                H("The square-cube representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n at least one and powerful there are naturals a and b with n equal to a "
                        + "squared times b cubed and with b squarefree. Mathlib decomposes n as d "
                        + "squared times c with c squarefree. For a prime p occurring in c, the "
                        + "squarefree condition puts its exponent in c at one, while the powerful "
                        + "condition puts its exponent in n at least at two; since that exponent "
                        + "is twice its exponent in d plus its exponent in c, the exponent in d is "
                        + "at least one. Comparing exponents at every prime gives c dividing d, "
                        + "and writing d as e times c turns d squared times c into e squared times "
                        + "c cubed, which is the stated representation with b equal to c. "
                        + "Uniqueness of the squarefree part is not claimed."))),
                DescribeRole.Theorem)),
        []));
}
