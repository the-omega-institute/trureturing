using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FinitePrimeTailSecondOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-square Abel tail through three logarithmic coefficients.",
        H("Native scoped implementation"),
        Blocks(
            Paragraph(Text("Native compiled scope only. The estimate is finite in both endpoints and uses the exact strict/inclusive prime interval. It does not claim an infinite tail, final16, or RH.")),
            Describe.Lean(DescribeId.Create("finiteprimetailsecondorder-tail-polynomial"),
                DeclarationHandle.Create(Prefix + "tailPolynomial"), H("Retained endpoint polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("tailPolynomial x is 1/(x log x)-1/(x log(x)^2)+2/(x log(x)^3), with both endpoint values retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finiteprimetailsecondorder-finite-square-three-terms"),
                DeclarationHandle.Create(Prefix + "finite_square_three_terms"), H("Uniform finite two-endpoint estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists X>1 such that every X<=y<=z satisfies abs(squareSum y z-(tailPolynomial y-tailPolynomial z)) <= 130/(y*log(y)^4). The proof combines the coefficient-25 four-term envelope, both endpoint errors, the finite integral error, and the exact K4/K5 model corrections."))), DescribeRole.Theorem)
        )));
}
