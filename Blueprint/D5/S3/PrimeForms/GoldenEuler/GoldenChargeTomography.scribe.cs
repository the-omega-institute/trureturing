using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GoldenEuler;

internal sealed class GoldenChargeTomographyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neutral and quadratic charge channels invert exactly to split and inert channels by the C2 Fourier transform.",
        H("Golden Charge Tomography"),
        Blocks(
            Theorem("split-channel-reconstruction", "split_channel_reconstruction",
                "The Split Channel Is Reconstructed Exactly", SplitChannelReconstructionFormula(),
                "Adding the neutral and signed charge channels isolates twice the split component.",
                "Division by two gives exact finite Fourier inversion and requires no analytic assumptions."),
            Theorem("inert-channel-reconstruction", "inert_channel_reconstruction",
                "The Inert Channel Is Reconstructed Exactly", InertChannelReconstructionFormula(),
                "Subtracting the signed charge channel from the neutral channel isolates twice the inert component.",
                "The identity is purely algebraic and does not make a statement about Dirichlet series or zeros."),
            Theorem("split-add-inert-indicator", "split_add_inert_indicator",
                "The Indicators Partition Unit Mass", SplitAddInertIndicatorFormula(),
                "The positive and negative charge indicators add to one for every real charge value.",
                "This partition identity is algebraic; it does not require the charge to equal plus or minus one."),
            Theorem("split-sub-inert-indicator", "split_sub_inert_indicator",
                "The Signed Indicator Difference Recovers Charge", SplitSubInertIndicatorFormula(),
                "The split indicator minus the inert indicator reproduces the original real charge.",
                "Together with the sum identity, this records the two-coordinate inverse transform only."),
            Theorem("split-indicator-pos-charge", "split_indicator_pos_charge",
                "Positive Charge Selects the Split Indicator", SplitIndicatorPosChargeFormula(),
                "At charge plus one, the split indicator has value one.",
                "The endpoint evaluation identifies the split channel without asserting a classification of inputs."),
            Theorem("inert-indicator-pos-charge", "inert_indicator_pos_charge",
                "Positive Charge Vanishes in the Inert Indicator", InertIndicatorPosChargeFormula(),
                "At charge plus one, the inert indicator has value zero.",
                "This is the complementary endpoint evaluation to the positive split indicator."),
            Theorem("split-indicator-neg-charge", "split_indicator_neg_charge",
                "Negative Charge Vanishes in the Split Indicator", SplitIndicatorNegChargeFormula(),
                "At charge minus one, the split indicator has value zero.",
                "The theorem evaluates the finite indicator and introduces no local Euler hypothesis."),
            Theorem("inert-indicator-neg-charge", "inert_indicator_neg_charge",
                "Negative Charge Selects the Inert Indicator", InertIndicatorNegChargeFormula(),
                "At charge minus one, the inert indicator has value one.",
                "This completes the two endpoint evaluations of the charge-channel transform."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula SplitChannelReconstructionFormula() => Reconstruction(
        F.Id("splitFromChannels"), F.Id("split"));

    private static Formula InertChannelReconstructionFormula() => Reconstruction(
        F.Id("inertFromChannels"), F.Id("inert"));

    private static Formula Reconstruction(Formula reconstruction, Formula result)
    {
        Formula split = F.Id("split"); Formula inert = F.Id("inert");
        return Statement([Typed(split, Reals()), Typed(inert, Reals())],
            Seq(Apply(reconstruction,
                    Call("neutralChannel", split, inert), Call("chargeChannel", split, inert)),
                Sp, Eq, Sp, result));
    }

    private static Formula SplitAddInertIndicatorFormula()
    {
        Formula charge = F.Id("charge");
        return Statement([Typed(charge, Reals())], Seq(
            Call("splitIndicator", charge), Sp, Plus, Sp, Call("inertIndicator", charge),
            Sp, Eq, Sp, D(1)));
    }

    private static Formula SplitSubInertIndicatorFormula()
    {
        Formula charge = F.Id("charge");
        return Statement([Typed(charge, Reals())], Seq(
            Call("splitIndicator", charge), Sp, Minus, Sp, Call("inertIndicator", charge),
            Sp, Eq, Sp, charge));
    }

    private static Formula SplitIndicatorPosChargeFormula() =>
        Statement([], Seq(Call("splitIndicator", D(1)), Sp, Eq, Sp, D(1)));

    private static Formula InertIndicatorPosChargeFormula() =>
        Statement([], Seq(Call("inertIndicator", D(1)), Sp, Eq, Sp, D(0)));

    private static Formula SplitIndicatorNegChargeFormula() =>
        Statement([], Seq(Call("splitIndicator", NegativeOne()), Sp, Eq, Sp, D(0)));

    private static Formula InertIndicatorNegChargeFormula() =>
        Statement([], Seq(Call("inertIndicator", NegativeOne()), Sp, Eq, Sp, D(1)));

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
    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);
    private static Formula NegativeOne() => Seq(Minus, D(1));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
