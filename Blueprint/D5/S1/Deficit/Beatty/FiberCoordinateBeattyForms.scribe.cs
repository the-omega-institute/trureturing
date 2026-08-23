using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class FiberCoordinateBeattyFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden fiber coordinates have exact displacement forms, an equation characterizes each fiber, and the proposed ceiling start fails at label one.",
        H("Displacement and Beatty Forms of Golden Fiber Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiber-coordinate-displacement-forms"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.fiber_coordinates_eq_displacement_forms"),
                H("Both fiber coordinates have exact displacement forms"),
                StatementSource.FromAuthor(CoordinateForms()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural index v, the first golden fiber coordinate is twice "
                        + "the displacement reading minus three times v, while the second is "
                        + "twice v minus the same displacement reading.")),
                    Paragraph(Text(
                        "The established Beatty formula for the displacement reading replaces "
                        + "the common golden-shift term in both coordinate definitions. Thus the "
                        + "two floor-defined coordinates and their integral linear forms agree "
                        + "simultaneously."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-fiber-membership-equation"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.mem_goldenFiber_iff"),
                H("Fiber membership is exactly the doubled displacement equation"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fiber labelled by an integer a is the level set where the first "
                        + "coordinate equals a. An index v belongs to this fiber exactly when "
                        + "twice its displacement reading equals three times v plus a.")),
                    Paragraph(Text(
                        "Substituting the first coordinate's displacement form turns the level-set "
                        + "condition into this equation without changing either direction of the "
                        + "equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ceiling-start-formula-fails-at-one"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.ceiling_start_formula_fails_at_one"),
                H("The proposed ceiling start fails at label one"),
                StatementSource.FromAuthor(CeilingCounterexample()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At label one, the golden-ratio square identity reduces phi minus phi "
                        + "squared to minus one. Its ceiling is therefore minus one, whereas its "
                        + "floor followed by adding one is zero, so the proposed ceiling start "
                        + "cannot equal the corrected floor-plus-one expression."))),
                DescribeRole.Theorem))));

    private static Formula CoordinateForms() => Disp(Seq(
        Forall, Sp, F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
        Comma, Esc,
        Operatorname, Grp(F.Id("fiberA")), Open, F.Id("v"), Close, Sp, Eq, Sp,
        D(2), Sp, Cdot, Sp,
        Operatorname, Grp(F.Id("displacementDecode")), Open, F.Id("v"), Close,
        Sp, Minus, Sp, D(3), Sp, Cdot, Sp, F.Id("v"),
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("fiberB")), Open, F.Id("v"), Close, Sp, Eq, Sp,
        D(2), Sp, Cdot, Sp, F.Id("v"), Sp, Minus, Sp,
        Operatorname, Grp(F.Id("displacementDecode")), Open, F.Id("v"), Close));

    private static Formula MembershipFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
        F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
        F.Id("v"), Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("goldenFiber")), Open, F.Id("a"), Close,
        Sp, Iff, Sp,
        D(2), Sp, Cdot, Sp,
        Operatorname, Grp(F.Id("displacementDecode")), Open, F.Id("v"), Close,
        Sp, Eq, Sp, D(3), Sp, Cdot, Sp, F.Id("v"), Sp, Plus, Sp, F.Id("a")));

    private static Formula CeilingCounterexample() => Disp(Seq(
        Operatorname, Grp(F.Id("ceil")), Open,
        Varphi, Sp, Minus, Sp, Varphi, Caret, Grp(D(2)), Close,
        Sp, Neq, Sp,
        Lfloor, Varphi, Sp, Minus, Sp, Varphi, Caret, Grp(D(2)), Rfloor,
        Sp, Plus, Sp, D(1)));
}
