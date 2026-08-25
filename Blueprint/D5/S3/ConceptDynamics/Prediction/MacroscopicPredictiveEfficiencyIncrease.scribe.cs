using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class MacroscopicPredictiveEfficiencyIncreaseDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Prediction/MacroscopicPredictiveEfficiencyIncrease."
            + "macroscopic_predictive_efficiency_strictly_increases";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing fresh noise strictly improves predictive information per represented bit.",
        H("Macroscopic Predictive Efficiency Increase"),
        Blocks(Describe.Lean(
            DescribeId.Create("macroscopic-predictive-efficiency-strictly-increases"),
            DeclarationHandle.Create(Declaration),
            H("Projection removes fresh noise while retaining absolute predictive information"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The microscopic state consists of a persistent fair bit and a fresh fair "
                        + "noise bit. The displayed joint law gives mass one eighth to exactly "
                        + "the transitions that preserve the first coordinate.")),
                Paragraph(Text(
                    "Both microscopic time marginals are uniform on four states. Entropy and "
                        + "mutual information are converted from the repository's natural-log "
                        + "units to bits by division by log two.")),
                Paragraph(Text(
                    "The coarse concept keeps the persistent coordinate. Its marginal is fair, "
                        + "its entropy and mutual information are each one bit, and its efficiency "
                        + "is one rather than one half. Absolute mutual information stays equal."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula TheoremFormula()
    {
        Formula zero = D(0);
        Formula one = D(1);
        Formula two = D(2);
        Formula four = D(4);
        Formula eight = D(8);
        Formula bit = F.Id("b");
        Formula state = F.Id("x");
        Formula persistent = F.Id("s");
        Formula persistentNext = F.Id("sNext");
        Formula noise = F.Id("n");
        Formula noiseNext = F.Id("nNext");
        Formula microscopic = F.Id("p");
        Formula coarse = F.Id("c");
        Formula macroscopic = F.Id("q");
        Formula half = new Formula.Fraction(one, two);
        Formula quarter = new Formula.Fraction(one, four);
        Formula eighth = new Formula.Fraction(one, eight);

        Formula microscopicState = Pair(persistent, noise);
        Formula nextMicroscopicState = Pair(persistentNext, noiseNext);
        Formula persistentTransition =
            Pair(microscopicState, Pair(persistent, noiseNext));
        Formula changedTransition = Pair(microscopicState, nextMicroscopicState);

        Formula entropyBits(Formula law) =>
            new Formula.Fraction(Call("shannonEntropy", law), Call("log", two));
        Formula informationBits(Formula law) =>
            new Formula.Fraction(Call("mutualInformation", law), Call("log", two));
        Formula efficiency(Formula law) =>
            new Formula.Fraction(informationBits(law), entropyBits(Call("marginal", law)));

        Formula model = Seq(
            Forall, Sp, persistent, Comma, Sp, persistentNext, Comma, Sp,
            noise, Comma, Sp, noiseNext, InMacro, Sp, F.Id("Bool"), Comma,
            RowBreak, Grp(),
            Apply(microscopic, changedTransition), Sp, Eq, Sp,
            Call("if", Seq(persistent, Sp, Eq, Sp, persistentNext), eighth, zero),
            Comma, RowBreak, Grp(),
            Apply(coarse, microscopicState), Sp, Eq, Sp, persistent,
            Comma, Sp, macroscopic, Sp, Eq, Sp,
            Call("coarseGrainedJoint", microscopic, coarse));

        Formula conclusion = Seq(
            Call("ProbabilityLaw", microscopic), Sp, Land, RowBreak, Grp(),
            Forall, Sp, persistent, Comma, Sp, noise, Comma, Sp, noiseNext,
            Comma, Sp, Apply(microscopic, persistentTransition), Sp, Eq, Sp, eighth,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, persistent, Comma, Sp, persistentNext, Comma, Sp,
            noise, Comma, Sp, noiseNext, Comma, Sp,
            persistent, Sp, Neq, Sp, persistentNext, Sp, Rightarrow, Sp,
            Apply(microscopic, changedTransition), Sp, Eq, Sp, zero,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp,
            Apply(Call("marginal", microscopic), state), Sp, Eq, Sp, quarter,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp,
            Apply(Call("marginal", Call("swap", microscopic)), state),
            Sp, Eq, Sp, quarter,
            Sp, Land, RowBreak, Grp(),
            entropyBits(Call("marginal", microscopic)), Sp, Eq, Sp, two,
            Sp, Land, Sp, informationBits(microscopic), Sp, Eq, Sp, one,
            Sp, Land, RowBreak, Grp(),
            efficiency(microscopic), Sp, Eq, Sp, half,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, bit, Comma, Sp,
            Apply(Call("marginal", macroscopic), bit), Sp, Eq, Sp, half,
            Sp, Land, RowBreak, Grp(),
            entropyBits(Call("marginal", macroscopic)), Sp, Eq, Sp, one,
            Sp, Land, Sp, informationBits(macroscopic), Sp, Eq, Sp, one,
            Sp, Land, RowBreak, Grp(),
            efficiency(macroscopic), Sp, Eq, Sp, one,
            Sp, Land, Sp, efficiency(microscopic), Sp, Lt, Sp,
            efficiency(macroscopic),
            Sp, Land, RowBreak, Grp(),
            Call("mutualInformation", macroscopic), Sp, Eq, Sp,
            Call("mutualInformation", microscopic));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            model, Colon, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
