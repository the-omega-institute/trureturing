using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class NormativeScaleChoiceReversalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal."
            + "normative_scale_choice_reversal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal doctrine probabilities and fixed internal rankings do not determine "
            + "a unique action across utility scales.",
        H("Normative Scale Choice Reversal"),
        Blocks(Describe.Lean(
            DescribeId.Create("normative-scale-choice-reversal"),
            DeclarationHandle.Create(Declaration),
            H("Doctrine probability does not determine cross-scale choice"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public model has two Boolean doctrines and two Boolean actions. "
                        + "Both doctrines retain probability one half under both utility "
                        + "scales.")),
                Paragraph(Text(
                    "The first doctrine assigns positive utility only to action a, while "
                        + "the second assigns positive utility only to action b. All "
                        + "pairwise within-doctrine comparisons are identical across the "
                        + "two positive scale pairs.")),
                Paragraph(Text(
                    "The probability-weighted values are alpha over two and beta over "
                        + "two. Opposite cross-doctrine magnitudes therefore select action "
                        + "a under the first scaling and action b under the second.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found no exact theorem. The "
                        + "construction uses ordered-field arithmetic directly."))),
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

    private static Formula TheoremFormula()
    {
        Formula alphaFirst = F.Id("alphaFirst");
        Formula betaFirst = F.Id("betaFirst");
        Formula alphaSecond = F.Id("alphaSecond");
        Formula betaSecond = F.Id("betaSecond");
        Formula probability = F.Id("p");
        Formula utility = F.Id("u");
        Formula expected = F.Id("EU");
        Formula doctrine = F.Id("d");
        Formula leftAction = F.Id("x");
        Formula rightAction = F.Id("y");
        Formula actionA = F.Id("a");
        Formula actionB = F.Id("b");
        Formula doctrineFirst = F.Id("first");
        Formula doctrineSecond = F.Id("second");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));

        Formula parameters = Seq(
            alphaFirst, Comma, Sp, betaFirst, Comma, Sp,
            alphaSecond, Comma, Sp, betaSecond, Sp, InMacro, Sp, reals,
            Comma, Sp,
            D(0), Sp, Lt, Sp, alphaFirst, Comma, Sp,
            D(0), Sp, Lt, Sp, betaFirst, Comma, Sp,
            D(0), Sp, Lt, Sp, alphaSecond, Comma, Sp,
            D(0), Sp, Lt, Sp, betaSecond, Comma,
            RowBreak, Grp(),
            betaFirst, Sp, Lt, Sp, alphaFirst, Comma, Sp,
            alphaSecond, Sp, Lt, Sp, betaSecond);

        Formula firstCoordinates = Seq(
            Apply(utility, alphaFirst, betaFirst, doctrineFirst, actionA),
            Sp, Eq, Sp, alphaFirst, Comma, Sp,
            Apply(utility, alphaFirst, betaFirst, doctrineFirst, actionB),
            Sp, Eq, Sp, D(0), Comma, Sp,
            Apply(utility, alphaFirst, betaFirst, doctrineSecond, actionA),
            Sp, Eq, Sp, D(0), Comma, Sp,
            Apply(utility, alphaFirst, betaFirst, doctrineSecond, actionB),
            Sp, Eq, Sp, betaFirst);
        Formula secondCoordinates = Seq(
            Apply(utility, alphaSecond, betaSecond, doctrineFirst, actionA),
            Sp, Eq, Sp, alphaSecond, Comma, Sp,
            Apply(utility, alphaSecond, betaSecond, doctrineFirst, actionB),
            Sp, Eq, Sp, D(0), Comma, Sp,
            Apply(utility, alphaSecond, betaSecond, doctrineSecond, actionA),
            Sp, Eq, Sp, D(0), Comma, Sp,
            Apply(utility, alphaSecond, betaSecond, doctrineSecond, actionB),
            Sp, Eq, Sp, betaSecond);

        Formula rankings = Seq(
            Forall, Sp, doctrine, Comma, Sp, leftAction, Comma, Sp, rightAction,
            Comma, Sp,
            Open,
            Apply(utility, F.Id("alphaFirst"), F.Id("betaFirst"),
                doctrine, leftAction),
            Sp, Gt, Sp,
            Apply(utility, F.Id("alphaFirst"), F.Id("betaFirst"),
                doctrine, rightAction),
            Close, Sp, Iff, Sp,
            Open,
            Apply(utility, F.Id("alphaSecond"), F.Id("betaSecond"),
                doctrine, leftAction),
            Sp, Gt, Sp,
            Apply(utility, F.Id("alphaSecond"), F.Id("betaSecond"),
                doctrine, rightAction),
            Close);

        Formula aggregate = Seq(
            Apply(expected, F.Id("alphaFirst"), F.Id("betaFirst"), actionA),
            Sp, Eq, Sp, Seq(Frac, Grp(F.Id("alphaFirst")), Grp(D(2))), Comma, Sp,
            Apply(expected, F.Id("alphaFirst"), F.Id("betaFirst"), actionB),
            Sp, Eq, Sp, Seq(Frac, Grp(F.Id("betaFirst")), Grp(D(2))), Comma,
            RowBreak, Grp(),
            Apply(expected, F.Id("alphaSecond"), F.Id("betaSecond"), actionA),
            Sp, Eq, Sp, Seq(Frac, Grp(F.Id("alphaSecond")), Grp(D(2))), Comma, Sp,
            Apply(expected, F.Id("alphaSecond"), F.Id("betaSecond"), actionB),
            Sp, Eq, Sp, Seq(Frac, Grp(F.Id("betaSecond")), Grp(D(2))));

        Formula reversal = Seq(
            Apply(expected, F.Id("alphaFirst"), F.Id("betaFirst"), actionA),
            Sp, Gt, Sp,
            Apply(expected, F.Id("alphaFirst"), F.Id("betaFirst"), actionB),
            Sp, Land, Sp,
            Apply(expected, F.Id("alphaSecond"), F.Id("betaSecond"), actionB),
            Sp, Gt, Sp,
            Apply(expected, F.Id("alphaSecond"), F.Id("betaSecond"), actionA));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            parameters, Comma,
            RowBreak, Grp(),
            Forall, Sp, doctrine, Comma, Sp,
            Apply(probability, doctrine), Sp, Eq, Sp, half, Comma,
            RowBreak, Grp(),
            firstCoordinates, Comma,
            RowBreak, Grp(),
            secondCoordinates, Comma,
            RowBreak, Grp(),
            rankings, Comma,
            RowBreak, Grp(),
            aggregate, Comma,
            RowBreak, Grp(),
            reversal, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
