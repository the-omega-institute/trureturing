using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisTable",
            "Finite prime-indexed canonical W digits encode factorization exponents."),
        H("Prime-Axis W-Digit Tables"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("finite-prime-axis-table-and-product-decode"),
                DescribeKind.Theorem,
                H("Finite prime-axis table and product decode"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "An outer finitely supported table assigns canonical binary nonadjacent W digits to prime axes. The theorem exposes finite global support, each W-weighted exponent sum, and the corresponding finite prime-power product decode.")))))));
}
