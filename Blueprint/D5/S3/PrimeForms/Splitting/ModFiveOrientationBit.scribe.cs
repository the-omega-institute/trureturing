using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class ModFiveOrientationBitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The modulo-five orientation bit separates every binary three-ring profile fiber without defining a binary group character.",
        H("Modulo-Five Orientation Bit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mod-five-orientation-separates-fibers-but-is-not-a-character"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Splitting/ModFiveOrientationBit."
                        + "mod_five_orientation_separates_fibers_but_is_not_homomorphic"),
                H("The missing bit separates fibers but is not a group character"),
                StatementSource.FromAuthor(OrientationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a unit class u modulo sixty, modFiveOrientation(u) is zero when "
                            + "the residue of u modulo five is 1 or 2, and is one when that "
                            + "residue is 3 or 4.")),
                    Paragraph(Text(
                        "Every three-ring profile fiber has exactly two unit classes. Equal "
                            + "orientation bits on two classes in the same fiber force those "
                            + "classes to be equal, so the bit distinguishes the two classes.")),
                    Paragraph(Text(
                        "The contrast is structural: the bit does not send multiplication in "
                            + "the unit group to addition modulo two. Concretely, the class of "
                            + "seven has bit zero while its square, the class of forty-nine, "
                            + "has bit one.")),
                    Paragraph(Text(
                        "Repository search supplied the exact two-element-fiber theorem and it "
                            + "is applied directly. Searches of the repository and pinned "
                            + "Mathlib found no theorem packaging the orientation test, its "
                            + "fiberwise separation, and the non-homomorphism contrast."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula OrientationFormula()
    {
        Formula profile = F.Id("t");
        Formula leftUnit = F.Id("u");
        Formula rightUnit = F.Id("v");
        Formula image = F.Id("triRingImage");
        Formula orientation = Seq(Omega, Underscore, Grp(D(5)));
        Formula unitsModSixty = Seq(
            Open, Mathbb, Grp(F.Id("Z")), Slash, D(6, 0),
            Mathbb, Grp(F.Id("Z")), Close, Caret, Grp(Times));
        Formula fiber = Seq(
            OpenBrace, leftUnit, Colon, Sp, unitsModSixty, Sp, Mid, Sp,
            Apply(image, leftUnit), Sp, Eq, Sp, profile, CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open,
            Open, Forall, Sp, profile, Colon, Sp, F.Id("ThreeRingProfile"),
            Comma, Sp, Vert, Sp, fiber, Sp, Vert, Sp, Eq, Sp, D(2), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, profile, Colon, Sp, F.Id("ThreeRingProfile"),
            Comma, Sp, leftUnit, Comma, Sp, rightUnit, Colon, Sp, unitsModSixty,
            Comma, RowBreak, Grp(),
            Apply(image, leftUnit), Sp, Eq, Sp, profile, Sp, Land, Sp,
            Apply(image, rightUnit), Sp, Eq, Sp, profile, Sp, Land, RowBreak, Grp(),
            Apply(orientation, leftUnit), Sp, Eq, Sp,
            Apply(orientation, rightUnit), Sp, Rightarrow, Sp,
            leftUnit, Sp, Eq, Sp, rightUnit, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Neg, Open, Forall, Sp, leftUnit, Comma, Sp, rightUnit, Colon, Sp,
            unitsModSixty, Comma, RowBreak, Grp(),
            Apply(orientation, Seq(leftUnit, Sp, Times, Sp, rightUnit)),
            Sp, Eq, Sp, Apply(orientation, leftUnit), Sp, Plus, Sp,
            Apply(orientation, rightUnit), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
