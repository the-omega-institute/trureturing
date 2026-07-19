using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class NormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/Norm",
            "The golden norm is multiplicative and agrees with the scaled mathlib norm."),
        H("Golden Norm"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Norm"),
                Text(" defines `N(a+b*phi)=a^2+ab-b^2`. Multiplying an element by its conjugate eliminates the `phi` coordinate and produces this integer, which makes the multiplicativity proof a direct polynomial identity.")),
            Paragraph(
                Text("Under the doubled `Zsqrtd 5` coordinates from the carrier module, the mathlib norm is exactly four times the golden norm. This factor is the expected square of the coordinate scaling.")),
            new DocumentBlock.Describe(
                DescribeId.Create("two-square-norm-as-a-shared-interpretive-core"),
                DescribeKind.Remark,
                H("The two-square norm as a shared interpretive core"),
                DescribeStatement.FromFormula(Equal(
                    Call("gaussianNorm", Id("a"), Id("b")),
                    Add(
                        new Formula.Power(Id("a"), Num(2)),
                        new Formula.Power(Id("b"), Num(2))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source groups a^2+b^2 under four roles: the defining two-axis norm, the Gaussian norm, the modulus-four obstruction, and the splitting reading modulo a prime. It states that each role has its own theorem and that norm multiplicativity is the pivot used in the composition step. The vocabulary in which primes congruent to one split, primes congruent to three remain inert, and two ramifies is explicitly interpretive: the classification theorem is said not to depend on that Gaussian-integer language. A separate dynamical role is referenced but not added as a claim of this module.")))))));
}
