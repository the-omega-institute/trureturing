using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class SymmetricBernoulliSecondOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric two-point signal has quadratic Hellinger, log-affinity, and KL evidence with quartic remainders.",
        H("Symmetric Bernoulli Second-Order Evidence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-second-order"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder."
                        + "symmetric_bernoulli_second_order"),
                H("Weak symmetric bias produces quadratic evidence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On Bool, the positive-bias mass assigns one half plus delta to true "
                            + "and one half minus delta to false. The negative-bias mass swaps "
                            + "those two values. Thus the source laws are constructed directly "
                            + "from the two-point carrier rather than introduced through the "
                            + "claimed asymptotic coefficients.")),
                    Paragraph(Text(
                        "The frozen squared Hellinger distance, Bhattacharyya affinity, and "
                            + "real-valued finite KL divergence evaluate on this pair to the "
                            + "source closed forms. Rationalizing the square root controls the "
                            + "first remainder, while the pinned local logarithm estimate "
                            + "controls the other two.")),
                    Paragraph(Text(
                        "Each displayed remainder is bounded by a constant multiple of delta "
                            + "to the fourth in a neighborhood of zero. The three clauses are "
                            + "independent public conjuncts and use the exact Bool laws shown "
                            + "before the asymptotic statement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pow(Formula value, int exponent) =>
        Seq(value, Caret, Grp(D((byte)exponent)));

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula bit = F.Id("b");
        Formula positiveLaw = new Formula.Subscript(F.Id("P"), delta);
        Formula negativeLaw = new Formula.Subscript(F.Id("Q"), delta);
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula positiveMass = Call(
            "ite", bit,
            Seq(half, Sp, Plus, Sp, delta),
            Seq(half, Sp, Minus, Sp, delta));
        Formula negativeMass = Call(
            "ite", bit,
            Seq(half, Sp, Minus, Sp, delta),
            Seq(half, Sp, Plus, Sp, delta));
        Formula deltaSquared = Pow(delta, 2);
        Formula deltaFourth = Pow(delta, 4);
        Formula hellingerSquared = Pow(Call("H", positiveLaw, negativeLaw), 2);
        Formula affinity = Seq(
            Rho, Open, positiveLaw, Comma, Sp, negativeLaw, Close);
        Formula divergence = Seq(
            F.Id("D"), Underscore, Grp(F.Id("KL")),
            Open, positiveLaw, Comma, Sp, negativeLaw, Close);
        Formula remainder = Call("O", deltaFourth);

        return Disp(Seq(
            Forall, Sp, bit, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Bool")), Comma,
            RowBreak, Grp(),
            Apply(positiveLaw, bit), Sp, Colon, Eq, Sp, positiveMass, Comma, Sp,
            Apply(negativeLaw, bit), Sp, Colon, Eq, Sp, negativeMass, Semi,
            RowBreak, Grp(),
            delta, Sp, To, Sp, D(0), Colon, RowBreak, Grp(),
            Open, hellingerSquared, Sp, Eq, Sp,
            D(4), Sp, deltaSquared, Sp, Plus, Sp, remainder, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Minus, Log, Sp, affinity, Sp, Eq, Sp,
            D(2), Sp, deltaSquared, Sp, Plus, Sp, remainder, Close,
            Sp, Land, RowBreak, Grp(),
            Open, divergence, Sp, Eq, Sp,
            D(8), Sp, deltaSquared, Sp, Plus, Sp, remainder, Close, Dot));
    }
}
