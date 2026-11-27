using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicSignedOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed power returns are governed by the order in the unit group modulo its two global signs.",
        H("Signed orders for the Lucas residue clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-signed-orders-all-returns"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_dvd_iff_modEq"),
                H("All signed return lags"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The powers of a unit that return to either plus one or minus one modulo the "
                    + "full modulus occur exactly at multiples of its order in the quotient by "
                    + "the subgroup of the two global signs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lucas-signed-order-least-positive"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_isLeast"),
                H("Least positive signed return"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive modulus the signed order is positive and is the least positive "
                    + "exponent returning to one of the two signs. Modulus one has order one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lucas-signed-order-prime-five"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_three_mod_five_pow"),
                H("Signed periods for powers of five"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus 5^r, the signed order of three is one when r is zero, and "
                    + "twice 5^(r-1) when r is positive. At odd prime powers the signs are "
                    + "all square roots of one, allowing use of the exact order of nine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lucas-composite-mixed-sign-obstruction"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicSignedOrder.mixed_sign_mod91"),
                H("A composite modulus distinguishes local and global signs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus 91, the third power of three is neither global sign even though "
                    + "its square is one. This rules out replacing the signed return by an "
                    + "unrestricted square condition for composite moduli."))),
                DescribeRole.Theorem))));
}
