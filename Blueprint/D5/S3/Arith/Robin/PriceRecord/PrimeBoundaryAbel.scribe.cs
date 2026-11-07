using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PrimeBoundaryAbelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real-endpoint prime Abel suppliers.",
        H("Native scoped implementation"),
        Blocks(
            Paragraph(Text("Native compiled scope only. This provider retains the original real endpoints and the strict lower-excluded, upper-included interval (y,z]. It supplies finite Abel identities used by the quantitative and finite-tail declarations; it makes no final RH or exact-infimum claim.")),
            Describe.Lean(DescribeId.Create("primeboundaryabel-prime-count"),
                DeclarationHandle.Create(Prefix + "primeCount"), H("Prime count at a real endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("primeCount t is Nat.primeCounting floor(t), cast to the reals."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primeboundaryabel-prime-interval"),
                DeclarationHandle.Create(Prefix + "primeInterval"), H("Strict lower and inclusive upper prime interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("primeInterval y z is the filtered Finset.Ioc floor(y) floor(z), so a prime tied at y is excluded and a prime tied at z is included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primeboundaryabel-square-sum"),
                DeclarationHandle.Create(Prefix + "squareSum"), H("Finite prime-square sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("squareSum y z sums 1/p^2 over primeInterval y z, with both real endpoints retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primeboundaryabel-finite-prime-square-abel"),
                DeclarationHandle.Create(Prefix + "finite_prime_square_abel"), H("Exact finite Abel identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<y and y<=z, squareSum y z equals primeCount z/z^2 - primeCount y/y^2 + 2 times the finite integral of primeCount t/t^3 from y to z. The proof uses the native finite Ioc definition and no infinite tail."))), DescribeRole.Theorem)
        )));
}
