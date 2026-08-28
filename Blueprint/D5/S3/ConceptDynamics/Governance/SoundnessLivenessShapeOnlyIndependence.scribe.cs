using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class SoundnessLivenessShapeOnlyIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/SoundnessLivenessShapeOnlyIndependence."
            + "soundness_liveness_independent_of_shape_only_tests";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete judge model separates soundness, liveness, and shape-only tests.",
        H("Soundness, Liveness, and Shape-Only Tests"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("soundness-liveness-independent-of-shape-only-tests"),
                DeclarationHandle.Create(Declaration),
                H("Soundness and liveness are independent of shape-only tests"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Judge is Bool x Bool. Soundness reads the first coordinate, liveness "
                            + "reads the second, and shape is the first coordinate itself.")),
                    Paragraph(Text(
                        "The judges (true,false) and (false,true) witness both failed implications. "
                            + "The judges (true,false) and (true,true) have equal shape but opposite "
                            + "liveness.")),
                    Paragraph(Text(
                        "Consequently every test family constant on equal-shape fibers fails to "
                            + "characterize liveness. The declaration also includes the general "
                            + "version for every model with a same-shape liveness split."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Open, left, Sp, Leftrightarrow, Sp, right, Close);

    private static Formula ShapeInvariantLaw(
        Formula judge, Formula shape, Formula test)
    {
        Formula first = F.Id("j1");
        Formula second = F.Id("j2");
        return Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, judge, Comma, Sp,
            Apply(shape, first), Sp, Eq, Sp, Apply(shape, second), Sp,
            Rightarrow, Sp, IffFormula(Apply(test, first), Apply(test, second)));
    }

    private static Formula CharacterizesLaw(
        Formula judge, Formula live, Formula test)
    {
        Formula item = F.Id("j");
        return Seq(
            Forall, Sp, item, Colon, Sp, judge, Comma, Sp,
            IffFormula(Apply(test, item), Apply(live, item)));
    }

    private static Formula TheoremFormula()
    {
        Formula judge = F.Id("Judge");
        Formula sound = F.Id("sound");
        Formula live = F.Id("live");
        Formula shape = F.Id("shape");
        Formula test = F.Id("T");
        Formula trueFalse = Pair(F.Id("true"), F.Id("false"));
        Formula falseTrue = Pair(F.Id("false"), F.Id("true"));
        Formula trueTrue = Pair(F.Id("true"), F.Id("true"));
        Formula concreteStrong = Seq(
            Forall, Sp, test, Colon, Sp,
            judge, Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            Grp(ShapeInvariantLaw(judge, shape, test)), Sp, Rightarrow, Sp,
            Neg, Grp(CharacterizesLaw(judge, live, test)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Apply(sound, trueFalse), Sp, Land, Sp,
            Neg, Sp, Apply(live, trueFalse), Sp, Land, Sp,
            Apply(live, falseTrue), Sp, Land, Sp,
            Neg, Sp, Apply(sound, falseTrue), Sp, Land,
            RowBreak, Grp(),
            Apply(shape, trueFalse), Sp, Eq, Sp, Apply(shape, trueTrue), Sp, Land, Sp,
            Neg, IffFormula(Apply(live, trueFalse), Apply(live, trueTrue)), Sp, Land,
            RowBreak, Grp(),
            Neg, Grp(Forall, Sp, F.Id("j"), Colon, Sp, judge, Comma, Sp,
                Apply(sound, F.Id("j")), Sp, Rightarrow, Sp,
                Apply(live, F.Id("j"))), Sp, Land, Sp,
            Neg, Grp(Forall, Sp, F.Id("j"), Colon, Sp, judge, Comma, Sp,
                Apply(live, F.Id("j")), Sp, Rightarrow, Sp,
                Apply(sound, F.Id("j"))), Sp, Land,
            RowBreak, Grp(),
            Grp(concreteStrong), Sp, Land, Sp,
            Operatorname, Grp(F.Id("GeneralSameShapeLivenessSplitLaw")), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
