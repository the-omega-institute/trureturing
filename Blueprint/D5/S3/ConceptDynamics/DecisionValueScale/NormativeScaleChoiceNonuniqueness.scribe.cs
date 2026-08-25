using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class NormativeScaleChoiceNonuniquenessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceNonuniqueness."
            + "normative_scale_choice_nonuniqueness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive rescalings preserve both doctrines' internal rankings but "
            + "produce opposite equiprobable aggregate choices.",
        H("Normative Scale Choice Nonuniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("normative-scale-choice-nonuniqueness"),
            DeclarationHandle.Create(Declaration),
            H("Positive cross-doctrine rescaling reverses the selected action"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The witness uses the source carrier of two Boolean doctrines and "
                        + "two Boolean actions. The probability function is constantly one "
                        + "half, and the utility coordinates are alpha for the first "
                        + "doctrine's preferred action and beta for the second's.")),
                Paragraph(Text(
                    "The public statement quantifies the two positive scale pairs, exposes "
                        + "all within-doctrine comparisons as invariant, and states the two "
                        + "opposite strict aggregate inequalities. It introduces no "
                        + "metanormative record or permission-intersection consequence.")),
                Paragraph(Text(
                    "The qualitative list of possible metanormative decision principles is "
                        + "not promoted to inert formal fields. Repository search found the "
                        + "frozen arithmetic reversal theorem as the exact primitive, which "
                        + "is applied directly."))),
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
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula probability = F.Id("p");
        Formula utility = F.Id("u");
        Formula expected = F.Id("EU");
        Formula doctrine = F.Id("d");
        Formula leftAction = F.Id("x");
        Formula rightAction = F.Id("y");
        Formula actionA = F.Id("a");
        Formula actionB = F.Id("b");
        Formula firstDoctrine = F.Id("first");
        Formula secondDoctrine = F.Id("second");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula oneHalf = Seq(Frac, Grp(D(1)), Grp(D(2)));

        Formula positiveScales = Seq(
            D(0), Sp, Lt, Sp, alphaFirst, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, betaFirst, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, alphaSecond, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, betaSecond);
        Formula firstRanking = Seq(
            Apply(utility, alphaFirst, betaFirst, firstDoctrine, actionA),
            Sp, Gt, Sp,
            Apply(utility, alphaFirst, betaFirst, firstDoctrine, actionB),
            Sp, Land, Sp,
            Apply(utility, alphaFirst, betaFirst, secondDoctrine, actionB),
            Sp, Gt, Sp,
            Apply(utility, alphaFirst, betaFirst, secondDoctrine, actionA));
        Formula invariantRanking = Seq(
            Forall, Sp, doctrine, Comma, Sp, leftAction, Comma, Sp, rightAction,
            Comma, Sp,
            Open,
            Apply(utility, alphaFirst, betaFirst, doctrine, leftAction),
            Sp, Gt, Sp,
            Apply(utility, alphaFirst, betaFirst, doctrine, rightAction),
            Close, Sp, Iff, Sp,
            Open,
            Apply(utility, alphaSecond, betaSecond, doctrine, leftAction),
            Sp, Gt, Sp,
            Apply(utility, alphaSecond, betaSecond, doctrine, rightAction),
            Close);
        Formula reversal = Seq(
            Apply(expected, alphaFirst, betaFirst, actionA),
            Sp, Gt, Sp,
            Apply(expected, alphaFirst, betaFirst, actionB),
            Sp, Land, Sp,
            Apply(expected, alphaSecond, betaSecond, actionB),
            Sp, Gt, Sp,
            Apply(expected, alphaSecond, betaSecond, actionA));
        Formula probabilityDefinition = Seq(
            Apply(probability, doctrine), Sp, Eq, Sp, oneHalf);
        Formula utilityDefinition = Seq(
            Apply(utility, alpha, beta, doctrine, leftAction), Sp, Eq, Sp,
            Begin, Grp(F.Id("cases")),
            alpha, Comma, Amp,
            doctrine, Sp, Eq, Sp, firstDoctrine, Sp, Land, Sp,
            leftAction, Sp, Eq, Sp, actionA, RowBreak, Grp(),
            D(0), Comma, Amp,
            doctrine, Sp, Eq, Sp, firstDoctrine, Sp, Land, Sp,
            leftAction, Sp, Eq, Sp, actionB, RowBreak, Grp(),
            D(0), Comma, Amp,
            doctrine, Sp, Eq, Sp, secondDoctrine, Sp, Land, Sp,
            leftAction, Sp, Eq, Sp, actionA, RowBreak, Grp(),
            beta, Comma, Amp,
            doctrine, Sp, Eq, Sp, secondDoctrine, Sp, Land, Sp,
            leftAction, Sp, Eq, Sp, actionB,
            End, Grp(F.Id("cases")));
        Formula expectedDefinition = Seq(
            Apply(expected, alpha, beta, leftAction), Sp, Eq, Sp,
            Apply(probability, firstDoctrine), Sp, Cdot, Sp,
            Apply(utility, alpha, beta, firstDoctrine, leftAction),
            Sp, Plus, Sp,
            Apply(probability, secondDoctrine), Sp, Cdot, Sp,
            Apply(utility, alpha, beta, secondDoctrine, leftAction));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            alphaFirst, Comma, Sp, betaFirst, Comma, Sp,
            alphaSecond, Comma, Sp, betaSecond,
            Sp, InMacro, Sp, reals, Comma, RowBreak, Grp(),
            positiveScales, Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            probabilityDefinition, Comma, RowBreak, Grp(),
            utilityDefinition, Comma, RowBreak, Grp(),
            expectedDefinition, SemiSpace, RowBreak, Grp(),
            Open, firstRanking, Close, Sp, Land, RowBreak, Grp(),
            Open, invariantRanking, Close, Sp, Land, RowBreak, Grp(),
            reversal, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
