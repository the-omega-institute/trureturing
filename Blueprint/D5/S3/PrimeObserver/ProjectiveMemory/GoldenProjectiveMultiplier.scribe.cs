using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver.ProjectiveMemory;

internal sealed class GoldenProjectiveMultiplierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conjugate golden mode scales by minus the inverse golden ratio, while its ratio to the dominant mode scales by its inverse square.",
        H("Golden Projective Multiplier"),
        Blocks(
            Theorem(
                "golden-conjugate-eq-neg-inv",
                "golden_conjugate_eq_neg_inv",
                GoldenConjugateEqNegInvFormula(),
                "Golden Conjugate eq neg Inv",
                "The ambient stable eigenvalue is minus the inverse golden ratio.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "stable-dominant-ratio-eq-projective-multiplier",
                "stable_dominant_ratio_eq_projective_multiplier",
                StableDominantRatioEqProjectiveMultiplierFormula(),
                "Stable Dominant Ratio eq Projective Multiplier",
                "The ratio of stable and dominant eigenvalues is the exact projective completion multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "projective-defect-modal-step",
                "projective_defect_modal_step",
                ProjectiveDefectModalStepFormula(),
                "Projective Defect Modal Step",
                "One Fibonacci modal step multiplies the normalized defect by the projective multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "projective-multiplier-of-modal-laws",
                "projective_multiplier_of_modal_laws",
                ProjectiveMultiplierOfModalLawsFormula(),
                "Projective Multiplier Of Modal Laws",
                "Abstract recurrence form: ambient laws A' = φA and D' = ψD imply the projective law whenever the dominant coordinate is nonzero.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "forced-projective-step-zero",
                "forced_projective_step_zero",
                ForcedProjectiveStepZeroFormula(),
                "Forced Projective Step Zero",
                "This theorem establishes forced projective step zero in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-state-zero-forcing",
                "zero_state_zero_forcing",
                ZeroStateZeroForcingFormula(),
                "Zero State Zero Forcing",
                "A vanishing state with zero forcing remains zero in one step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "ambient-and-projective-multipliers-ne",
                "ambient_and_projective_multipliers_ne",
                AmbientAndProjectiveMultipliersNeFormula(),
                "Ambient And Projective Multipliers ne",
                "The ambient stable eigenvalue and projective multiplier encode different normalization levels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula GoldenConjugateEqNegInvFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Eq, Sp, Minus, F.Id("Real"), Dot, F.Id("goldenRatio"), Caret, Grp(Minus, D(1))));

private static Formula StableDominantRatioEqProjectiveMultiplierFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Slash, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier")));

private static Formula ProjectiveDefectModalStepFormula() => Statement(
    [Typed(Seq(F.Id("A")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("D")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("A"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("projectiveDefect"), Sp, Open, F.Id("goldenModalStep"), Sp, Open, F.Id("A"), Comma, Sp, F.Id("D"), Close, Close, Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Times, Sp, F.Id("projectiveDefect"), Sp, Open, F.Id("A"), Comma, Sp, F.Id("D"), Close));

private static Formula ProjectiveMultiplierOfModalLawsFormula() => Statement(
    [Typed(Seq(F.Id("A")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("D")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("A"), Apos), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("D"), Apos), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("A"), Sp, Neq, Sp, D(0)), Seq(F.Id("A"), Apos, Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Times, Sp, F.Id("A")), Seq(F.Id("D"), Apos, Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Times, Sp, F.Id("D"))],
        Seq(F.Id("D"), Apos, Sp, Slash, Sp, F.Id("A"), Apos, Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Times, Sp, Open, F.Id("D"), Sp, Slash, Sp, F.Id("A"), Close));

private static Formula ForcedProjectiveStepZeroFormula() => Statement(
    [Typed(Seq(F.Id("theta")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("forcedProjectiveStep"), Sp, F.Id("theta"), Sp, D(0), Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Times, Sp, F.Id("theta")));

private static Formula ZeroStateZeroForcingFormula() => Statement(
    [Typed(Seq(F.Id("forcing")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("forcing"), Sp, Eq, Sp, D(0))],
        Seq(F.Id("forcedProjectiveStep"), Sp, D(0), Sp, F.Id("forcing"), Sp, Eq, Sp, D(0)));

private static Formula AmbientAndProjectiveMultipliersNeFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Neq, Sp, F.Id("goldenProjectiveMultiplier")));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
