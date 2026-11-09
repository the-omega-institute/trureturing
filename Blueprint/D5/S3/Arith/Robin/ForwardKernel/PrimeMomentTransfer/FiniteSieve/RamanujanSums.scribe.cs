using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class RamanujanSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime power values and multiplicativity of finite Ramanujan sums.",
        H("Finite Ramanujan sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ramanujan-prime-power"),
                DeclarationHandle.Create(Prefix + "ramanujan_prime_power"),
                H("Ramanujan sums at prime powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p and natural j and k, c_(p^(k+1))(j) is p^(k+1) times the indicator that p^(k+1) divides j, minus p^k times the indicator that p^k divides j. The equality holds in the complex numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ramanujan-multiplicative"),
                DeclarationHandle.Create(Prefix + "ramanujan_multiplicative"),
                H("Multiplicativity of Ramanujan sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For coprime natural moduli m and n and every natural argument j, c_(mn)(j)=c_m(j)c_n(j) in the complex numbers. The divisor identity and Moebius inversion express this Ramanujan sum as a convolution of multiplicative arithmetic functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ramanujan-one"),
                DeclarationHandle.Create(Prefix + "ramanujan_one"),
                H("Ramanujan sum at modulus one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus one the Ramanujan sum equals one for every natural argument."))),
                DescribeRole.Theorem))));
}
