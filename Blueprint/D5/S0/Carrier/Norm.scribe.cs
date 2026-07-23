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
                DescribeId.Create("norm-powers"),
                DescribeKind.Theorem,
                H("Norm of a natural power"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/NormPowers.norm_pow")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The existing norm is packaged as a monoid homomorphism from `GoldenInt` to `Int`. Applying its standard power law gives the exact identity for every golden integer and every natural exponent, with no extra algebraic assumptions."))),
                LatexStatement.Create(@"$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n$$")),
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
                    "The source groups a^2+b^2 under four roles: the defining two-axis norm, the Gaussian norm, the modulus-four obstruction, and the splitting reading modulo a prime. It states that each role has its own theorem and that norm multiplicativity is the pivot used in the composition step. The vocabulary in which primes congruent to one split, primes congruent to three remain inert, and two ramifies is explicitly interpretive: the classification theorem is said not to depend on that Gaussian-integer language. A separate dynamical role is referenced but not added as a claim of this module.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("norm-euclidean-division"),
                DescribeKind.Theorem,
                H("Norm-Euclidean division"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/Euclidean.golden_division")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/Carrier/chatland1949euclidean")),
                Blocks(
                    Paragraph(Text(
                        "For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.")),
                    Paragraph(Text(
                        "If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.")),
                    Paragraph(Text(
                        "The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`."))),
                LatexStatement.Create(@"$$\forall a,b\in\mathbb{Z}[\varphi],\ b\neq 0 \Rightarrow \exists q,r\in\mathbb{Z}[\varphi],\ a=qb+r \land (r=0 \lor \lvert\operatorname{norm}(r)\rvert<\lvert\operatorname{norm}(b)\rvert)$$")))));
}
