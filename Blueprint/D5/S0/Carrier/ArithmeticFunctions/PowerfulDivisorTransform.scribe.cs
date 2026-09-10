using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier.ArithmeticFunctions;

internal sealed class PowerfulDivisorTransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powerful-divisor summation is an inverse Moebius transform and preserves multiplicativity.",
        H("Powerful-Divisor Transform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("powerful"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.Powerful"),
                H("Powerful natural numbers"),
                StatementSource.FromAuthor(PowerfulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero natural number is powerful exactly when the square of every "
                        + "prime dividing it also divides it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powerful-indicator"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulIndicator"),
                H("Characteristic function of powerful numbers"),
                StatementSource.FromAuthor(IndicatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This arithmetic function is the characteristic function A112526."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powerful-divisor-sum"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.powerfulDivisorSum"),
                H("Sum over powerful divisors"),
                StatementSource.FromAuthor(DivisorSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an arithmetic function f, the transformed value at n sums f(d) over "
                        + "the powerful divisors d of n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powerful-divisor-sum-eq-inverse-moebius"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform."
                        + "powerfulDivisorSum_eq_inverseMoebius"),
                H("Inverse Moebius transform identity"),
                StatementSource.FromAuthor(InverseMoebiusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The powerful-divisor sum is the Dirichlet convolution of the zeta "
                        + "arithmetic function with the pointwise product of A112526 and f."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("powerful-divisor-sum-is-multiplicative"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform."
                        + "powerfulDivisorSum_isMultiplicative"),
                H("Preservation of multiplicativity"),
                StatementSource.FromAuthor(MultiplicativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If f is multiplicative, then its sum over powerful divisors is also "
                        + "multiplicative."))),
                DescribeRole.Theorem))));

    private static Formula NaturalNumbers() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PowerfulFormula() => Disp(Seq(
        Call("Powerful", F.Id("n")), Sp, Equiv, Sp,
        F.Id("n"), Sp, Neq, Sp, D(0), Sp, Land, Sp,
        Forall, Sp, F.Id("p"), Comma, Sp,
        Open, Call("Prime", F.Id("p")), Sp, Land, Sp,
        F.Id("p"), Sp, Mid, Sp, F.Id("n"), Close, Sp, Rightarrow, Sp,
        F.Id("p"), Caret, Grp(D(2)), Sp, Mid, Sp, F.Id("n"), Dot));

    private static Formula IndicatorFormula() => Disp(Seq(
        Call("powerfulIndicator", F.Id("n")), Sp, Eq, Sp,
        Operatorname, Grp(F.Id("if")), Open,
        Call("Powerful", F.Id("n")), Comma, Sp, D(1), Comma, Sp, D(0), Close, Dot));

    private static Formula DivisorSumFormula() => Disp(Seq(
        Call("powerfulDivisorSum", F.Id("f"), F.Id("n")), Sp, Eq, Sp,
        Sum, Underscore, Grp(F.Id("d"), Sp, Mid, Sp, F.Id("n"), Comma, Sp,
            Call("Powerful", F.Id("d"))), Sp, Call("f", F.Id("d")), Dot));

    private static Formula InverseMoebiusFormula() => Disp(Seq(
        Call("powerfulDivisorSum", F.Id("f")), Sp, Eq, Sp,
        Zeta, Sp, Star, Sp,
        Open, F.Id("powerfulIndicator"), Sp, Cdot, Sp, F.Id("f"), Close, Dot));

    private static Formula MultiplicativeFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Colon, Sp,
        Call("ArithmeticFunction", NaturalNumbers(), F.Id("R")), Comma, Sp,
        Call("Multiplicative", F.Id("f")), Sp, Rightarrow, Sp,
        Call("Multiplicative", Call("powerfulDivisorSum", F.Id("f"))), Dot));
}
