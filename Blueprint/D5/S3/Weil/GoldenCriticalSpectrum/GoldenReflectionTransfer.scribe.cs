using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenReflectionTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection-paired golden gains are globally balanced, while pointwise neutrality occurs exactly at zero normal displacement.",
        H("Golden Reflection Transfer"),
        Blocks(
            Theorem("golden-transfer-gain-pos", "golden_transfer_gain_pos",
                "Every Golden Transfer Gain Is Positive", GoldenTransferGainPosFormula(),
                "The transfer gain is a real exponential and is strictly positive for every real normal displacement.",
                "This sign statement does not require the displacement to arise from a spectral point."),
            Theorem("golden-transfer-gain-neg", "golden_transfer_gain_neg",
                "Reflected Displacement Gives Reciprocal Gain", GoldenTransferGainNegFormula(),
                "Negating a normal displacement turns its exponential golden gain into the reciprocal gain.",
                "The identity expresses reflection symmetry pointwise and makes no neutrality claim."),
            Theorem("reflected-transfer-product-one", "reflected_transfer_product_one",
                "A Reflected Gain Pair Has Product One", ReflectedTransferProductOneFormula(),
                "For every displacement, its gain and the gain at the negative displacement multiply to one.",
                "This determinant-like paired balance holds even when neither member has unit gain."),
            Theorem("golden-transfer-gain-eq-one-iff", "golden_transfer_gain_eq_one_iff",
                "Unit Gain Characterizes Zero Displacement", GoldenTransferGainEqOneIffFormula(),
                "The golden transfer gain equals one exactly when the real normal displacement is zero.",
                "Strict positivity of the golden period makes the exponential coordinate injective at the unit value."),
            Theorem("reflected-pair-pointwise-neutral-iff", "reflected_pair_pointwise_neutral_iff",
                "Both Reflected Gains Are Unit Exactly on the Fixed Axis", ReflectedPairPointwiseNeutralIffFormula(),
                "A displacement and its reflection both have unit gain exactly at zero displacement.",
                "The conjunction enforces pointwise neutrality of both members, which is stronger than their automatic product balance."),
            Theorem("paired-balance-strictly-weaker", "paired_balance_strictly_weaker",
                "Paired Balance Is Strictly Weaker Than Pointwise Neutrality", PairedBalanceStrictlyWeakerFormula(),
                "At displacement one, the reflected gain pair still has product one while the positive-displacement gain is not one.",
                "This explicit witness separates global paired balance from the pointwise unit-gain condition."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenTransferGainPosFormula()
    {
        Formula delta = DeltaLower;
        return Statement([Typed(delta, Reals())], Seq(
            D(0), Sp, Lt, Sp, Call("goldenTransferGain", delta)));
    }

    private static Formula GoldenTransferGainNegFormula()
    {
        Formula delta = DeltaLower;
        return Statement([Typed(delta, Reals())], Seq(
            Call("goldenTransferGain", Seq(Minus, delta)), Sp, Eq, Sp,
            Inverse(Call("goldenTransferGain", delta))));
    }

    private static Formula ReflectedTransferProductOneFormula()
    {
        Formula delta = DeltaLower;
        return Statement([Typed(delta, Reals())], Seq(
            Call("goldenTransferGain", delta), Sp, Times, Sp,
            Call("goldenTransferGain", Seq(Minus, delta)), Sp, Eq, Sp, D(1)));
    }

    private static Formula GoldenTransferGainEqOneIffFormula()
    {
        Formula delta = DeltaLower;
        return Statement([Typed(delta, Reals())], Equivalence(
            Seq(Call("goldenTransferGain", delta), Sp, Eq, Sp, D(1)),
            Seq(delta, Sp, Eq, Sp, D(0))));
    }

    private static Formula ReflectedPairPointwiseNeutralIffFormula()
    {
        Formula delta = DeltaLower;
        Formula bothUnit = Conjunction(
            Seq(Call("goldenTransferGain", delta), Sp, Eq, Sp, D(1)),
            Seq(Call("goldenTransferGain", Seq(Minus, delta)), Sp, Eq, Sp, D(1)));
        return Statement([Typed(delta, Reals())], Equivalence(
            bothUnit, Seq(delta, Sp, Eq, Sp, D(0))));
    }

    private static Formula PairedBalanceStrictlyWeakerFormula()
    {
        Formula balanced = Seq(
            Call("goldenTransferGain", D(1)), Sp, Times, Sp,
            Call("goldenTransferGain", Seq(Minus, D(1))), Sp, Eq, Sp, D(1));
        Formula nonneutral = Seq(Call("goldenTransferGain", D(1)), Sp, Neq, Sp, D(1));
        return Statement([], Conjunction(balanced, nonneutral));
    }

    private static Formula Equivalence(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Leftrightarrow, Sp, Open, right, Close);

    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp);
            for (int index = 0; index < binders.Length; index++)
            {
                if (index > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(binders[index]);
            }
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Inverse(Formula value) => Seq(Grp(value), Caret, Grp(Minus, D(1)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
