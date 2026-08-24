using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class ThreeRingProfileFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gaussian, Eisenstein, and golden readings on units modulo sixty realize every split-inert profile exactly twice.",
        H("Three-Ring Profile Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-ring-profile-map-has-two-element-fibers"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers."
                        + "tri_ring_image_surjective_with_fibers_of_card_two"),
                H("Every three-ring profile has exactly two unit classes"),
                StatementSource.FromAuthor(ThreeRingProfileFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a unit class modulo sixty, the Gaussian coordinate records whether its "
                            + "residue is 1 modulo 4, the Eisenstein coordinate records whether it is "
                            + "1 modulo 3, and the golden coordinate records whether it is 1 or 4 "
                            + "modulo 5.")),
                    Paragraph(Text(
                        "These three readings jointly attain every combination of split and inert "
                            + "coordinates. Moreover, each profile is attained by exactly two unit "
                            + "classes, so the unit classes are partitioned into uniform two-element "
                            + "fibers over the eight possible profiles."))),
                DescribeRole.Theorem))));

    private static Formula ThreeRingProfileFormula()
    {
        Formula profile = F.Id("t");
        Formula unit = F.Id("u");
        Formula unitsModSixty = Seq(
            Open, Mathbb, Grp(F.Id("Z")), Slash, D(6, 0),
            Mathbb, Grp(F.Id("Z")), Close, Caret, Grp(Times));
        Formula fiber = Seq(
            OpenBrace, unit, Colon, Sp, unitsModSixty, Sp, Mid, Sp,
            Call("triRingImage", unit), Sp, Eq, Sp, profile, CloseBrace);

        return Disp(Seq(
            Call("Surjective", F.Id("triRingImage")), Sp, Land, RowBreak,
            Forall, Sp, profile, Colon, Sp, F.Id("ThreeRingProfile"), Comma, Sp,
            Vert, Sp, fiber, Sp, Vert, Sp, Eq, Sp, D(2), Dot));
    }
}
