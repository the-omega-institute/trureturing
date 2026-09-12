using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class DirectImageComplementSaturationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation."
        + "image_complement_iff_saturated";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective images preserve complements exactly on unions of whole fibers.",
        H("Direct Image Complement Saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("image-complement-iff-saturated"),
                DeclarationHandle.Create(Declaration),
                H("Direct image preserves complement exactly on saturated sets"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f map the source carrier X onto the output carrier B, and let A "
                            + "be any subset of X. The complements are taken in X and B, "
                            + "respectively. No finiteness or injectivity assumption is required.")),
                    Paragraph(Text(
                        "The equation A = preimage(f, image(f, A)) says that each readout fiber "
                            + "is either entirely selected or entirely excluded. In this case "
                            + "the image of the excluded states is exactly the excluded output set.")),
                    Paragraph(Text(
                        "Conversely, if a selected and an excluded state share a readout, that "
                            + "readout belongs to both images. The complement equation rules out "
                            + "such a mixed fiber, so the selected set must be saturated."))),
                DescribeRole.Theorem))));

    private static Formula CriterionFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("B");
        Formula readout = F.Id("f");
        Formula selected = F.Id("A");
        Formula image = Call("image", readout, selected);
        Formula complementEquality = Seq(
            Call("image", readout, Call("complement", selected)), Sp, Eq, Sp,
            Call("complement", image));
        Formula saturation = Seq(
            selected, Sp, Eq, Sp, Call("preimage", readout, image));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, target, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(), readout, Colon, Sp, source, Sp, To, Sp, target, Comma, Sp,
            selected, Colon, Sp, Call("Set", source), Comma,
            RowBreak, Grp(), Call("Surjective", readout), Sp, Rightarrow, Sp,
            Open, complementEquality, Sp, Iff, Sp, saturation, Close, Dot));
    }
}
