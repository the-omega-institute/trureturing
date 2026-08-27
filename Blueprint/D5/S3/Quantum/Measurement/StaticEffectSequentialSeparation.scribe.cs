using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class StaticEffectSequentialSeparationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation."
            + "same_effects_different_two_step_joint_law";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal instrument effects do not determine sequential outcome laws.",
        H("Static Effect And Sequential Law Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("same-effects-different-two-step-joint-law"),
            DeclarationHandle.Create(Declaration),
            H("Equal effects can yield different two-step weights"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two Boolean-outcome qubit instruments are constructed explicitly. "
                        + "The first measures the computational projections, while the second "
                        + "applies the canonical bit flip after the same coordinate branch.")),
                Paragraph(Text(
                    "Their effect matrices agree outcome by outcome and both effect families "
                        + "sum to the identity. Starting from the basis-zero density after the "
                        + "false branch, however, the complementary second effect has weight "
                        + "zero for the projective instrument and weight one for the flipped "
                        + "instrument.")),
                Paragraph(Text(
                    "The branch maps and effect maps are displayed from their Kraus formulas. "
                        + "Thus the static agreement and sequential separation use the same "
                        + "constructed instruments rather than independent witnesses."))),
            DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula LabeledIndexed(Formula value, Formula label, Formula index) =>
        Seq(value, Caret, Grp(label), Underscore, Grp(index));

    private static Formula Adjoint(Formula value) =>
        Seq(Grp(value), Caret, Grp(Star));

    private static Formula TheoremFormula()
    {
        Formula outcome = F.Id("a");
        Formula rho = Rho;
        Formula family = F.Id("M");
        Formula projective = F.Id("L");
        Formula flipped = F.Id("J");
        Formula matrixType = F.Id("QubitMatrix");
        Formula boolType = F.Id("Bool");
        Formula familyType = Seq(boolType, Sp, To, Sp, matrixType);
        Formula zeroProjection = Indexed(F.Id("P"), D(0));
        Formula oneProjection = Indexed(F.Id("P"), D(1));
        Formula projectiveKraus = LabeledIndexed(F.Id("K"), projective, outcome);
        Formula flippedKraus = LabeledIndexed(F.Id("K"), flipped, outcome);
        Formula genericKraus = Indexed(family, outcome);
        Formula genericEffect = LabeledIndexed(F.Id("E"), family, outcome);
        Formula genericBranch = Seq(
            Mathcal, Grp(F.Id("I")), Caret, Grp(family), Underscore, Grp(outcome),
            Open, rho, Close);
        Formula projectiveEffect = LabeledIndexed(F.Id("E"), projective, outcome);
        Formula flippedEffect = LabeledIndexed(F.Id("E"), flipped, outcome);
        Formula falseOutcome = F.Id("false");
        Formula projectiveFalseBranch = Seq(
            Mathcal, Grp(F.Id("I")), Caret, Grp(projective),
            Underscore, Grp(falseOutcome), Open, zeroProjection, Close);
        Formula flippedFalseBranch = Seq(
            Mathcal, Grp(F.Id("I")), Caret, Grp(flipped),
            Underscore, Grp(falseOutcome), Open, zeroProjection, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            zeroProjection, Colon, Sp, matrixType, Sp, Eq, Sp,
            F.Id("basisZeroDensity"), Comma, Sp,
            oneProjection, Colon, Sp, matrixType, Sp, Eq, Sp,
            F.Id("I"), Sp, Minus, Sp, zeroProjection, Semi, RowBreak, Grp(),
            projectiveKraus, Colon, Sp, matrixType, Sp, Eq, Sp,
            Call("if", outcome, oneProjection, zeroProjection), Comma, Sp,
            outcome, Colon, Sp, boolType, Semi, RowBreak, Grp(),
            flippedKraus, Colon, Sp, matrixType, Sp, Eq, Sp,
            F.Id("qubitX"), Sp, Cdot, Sp, projectiveKraus, Comma, Sp,
            outcome, Colon, Sp, boolType, Semi, RowBreak, Grp(),
            genericEffect, Colon, Sp, matrixType, Sp, Eq, Sp,
            Adjoint(genericKraus), Sp, Cdot, Sp, genericKraus, Comma, Sp,
            family, Colon, Sp, familyType, Comma, Sp,
            outcome, Colon, Sp, boolType, Semi, RowBreak, Grp(),
            genericBranch, Colon, Sp, matrixType, Sp, Eq, Sp,
            genericKraus, Sp, Cdot, Sp, rho, Sp, Cdot, Sp, Adjoint(genericKraus),
            Comma, Sp, family, Colon, Sp, familyType, Comma, Sp,
            outcome, Colon, Sp, boolType, Comma, Sp,
            rho, Colon, Sp, matrixType, Semi, RowBreak, Grp(),
            Open, Forall, Sp, outcome, Colon, Sp, boolType, Comma, Sp,
            projectiveEffect, Sp, Eq, Sp, flippedEffect, Close,
            Sp, Land, RowBreak, Grp(),
            Sum, Underscore, Grp(outcome, Sp, InMacro, Sp, boolType), Sp,
            projectiveEffect, Sp, Eq, Sp, F.Id("I"), Sp, Land, RowBreak, Grp(),
            Sum, Underscore, Grp(outcome, Sp, InMacro, Sp, boolType), Sp,
            flippedEffect, Sp, Eq, Sp, F.Id("I"), Sp, Land, RowBreak, Grp(),
            Call("bornProbability", projectiveFalseBranch, oneProjection),
            Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Call("bornProbability", flippedFalseBranch, oneProjection),
            Sp, Eq, Sp, D(1), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
