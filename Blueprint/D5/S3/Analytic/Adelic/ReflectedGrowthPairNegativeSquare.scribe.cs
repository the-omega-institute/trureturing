using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ReflectedGrowthPairNegativeSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected exponential pair exchanges under time reversal, remains reciprocal, "
            + "and leaves the negative-square discriminant after first-order cancellation.",
        H("Reflected Growth Pair and Negative-Square Discriminant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-growth-pair-definition"),
                DeclarationHandle.Create(Prefix + "reflectedGrowthPair"),
                H("The reflected exponential pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two coordinates are exp(delta times t) and exp minus delta times t. "
                        + "They retain branch orientation instead of immediately collapsing to "
                        + "a symmetric cosh readout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("swap-pair-definition"),
                DeclarationHandle.Create(Prefix + "swapPair"),
                H("The branch-exchange involution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "swapPair exchanges the two coordinates. The Lean module separately proves "
                        + "that applying this exchange twice restores every pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflected-generator-definition"),
                DeclarationHandle.Create(Prefix + "reflectedGenerator"),
                H("The reflected generator rates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generator is the ordered pair (delta, minus delta). Its first-order "
                        + "trace cancels while its determinant retains the second-order split."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflection-pair-discriminant-definition"),
                DeclarationHandle.Create(Prefix + "reflectionPairDiscriminant"),
                H("The reflection-pair discriminant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The discriminant is the product of the two reflected generator rates. "
                        + "The main theorem identifies it exactly with minus delta squared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflected-growth-sum-definition"),
                DeclarationHandle.Create(Prefix + "reflectedGrowthSum"),
                H("The branch-forgetting symmetric readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The symmetric readout adds the expanding and contracting branches. It "
                        + "forgets which branch is which and therefore becomes even in time."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflected-growth-pair-negative-square"),
                DeclarationHandle.Create(Prefix + "reflected_growth_pair_negative_square"),
                H("Reflection leaves a negative-square invariant"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Time reversal exchanges the two exponential branches, while their "
                            + "pointwise product remains one. At generator level the trace is "
                            + "zero and the determinant is minus delta squared.")),
                    Paragraph(Text(
                        "The same invariant appears in the characteristic factorization "
                            + "(r minus delta)(r plus delta) equals r squared minus delta squared. "
                            + "This is a general scalar theorem and carries no completed-zeta or "
                            + "Riemann-hypothesis premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-orientation"),
                DeclarationHandle.Create(Prefix +
                    "reflected_growth_pair_forward_orientation"),
                H("Positive time separates expansion from contraction"),
                StatementSource.FromAuthor(OrientationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive delta and positive time, the first branch is strictly above "
                        + "one and the reflected branch is strictly below one. Reversing time "
                        + "exchanges these roles through the branch-swap theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-readout-even"),
                DeclarationHandle.Create(Prefix + "reflected_growth_sum_even"),
                H("The symmetric observer is even in time"),
                StatementSource.FromAuthor(EvenFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adding the two branches removes their orientation label. The resulting "
                        + "readout has identical values at t and minus t, which explains why a "
                        + "branch-forgetting observer is first-order blind to the split."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula PowerTwo(Formula value) =>
        Seq(value, Caret, Grp(D(2)));

    private static Formula Typed(Formula value) =>
        Seq(value, Colon, Sp, Reals());

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

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        Formula spectral = F.Id("r");
        Formula pair = Call("reflectedGrowthPair", delta, time);
        Formula generator = Call("reflectedGenerator", delta);
        Formula negativeTime = Seq(Minus, time);
        Formula negativeSquare = Seq(Minus, PowerTwo(delta));
        Formula leftFactor = Grp(Seq(spectral, Sp, Minus, Sp, delta));
        Formula rightFactor = Grp(Seq(spectral, Sp, Plus, Sp, delta));
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            Typed(spectral), Comma, Sp,
            Call("swapPair", pair), Sp, Eq, Sp,
            Call("reflectedGrowthPair", delta, negativeTime), Sp, Land, Sp,
            Call("fst", pair), Sp, Cdot, Sp, Call("snd", pair), Sp, Eq, Sp,
            D(1), Sp, Land, Sp,
            Call("pairTrace", generator), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Call("reflectionPairDiscriminant", delta), Sp, Eq, Sp,
            negativeSquare, Sp, Land, Sp,
            leftFactor, rightFactor, Sp, Eq, Sp,
            PowerTwo(spectral), Sp, Minus, Sp, PowerTwo(delta), Dot));
    }

    private static Formula OrientationFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        Formula pair = Call("reflectedGrowthPair", delta, time);
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, time, Sp, Rightarrow, Sp,
            D(1), Sp, Lt, Sp, Call("fst", pair), Sp, Land, Sp,
            Call("snd", pair), Sp, Lt, Sp, D(1), Dot));
    }

    private static Formula EvenFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            Call("reflectedGrowthSum", delta, Seq(Minus, time)), Sp, Eq, Sp,
            Call("reflectedGrowthSum", delta, time), Dot));
    }
}
