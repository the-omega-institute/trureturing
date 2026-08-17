using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DefectComposition;

internal sealed class StrictDefectCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict difference defects add exactly under map composition.",
        H("Strict Defect Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-defect-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/DefectComposition/StrictDefectComposition."
                        + "strict_defect_composition"),
                H("Strict difference defects form an additive chain"),
                StatementSource.FromAuthor(Disp(Seq(
                    DeltaLower, Underscore, Grp(F.Id("M")), Open,
                    F.Id("r"), Circ, Sp, F.Id("q"), Semi,
                    F.Id("x"), Comma, F.Id("y"), Close, Sp, Eq, Sp,
                    DeltaLower, Underscore, Grp(F.Id("M")), Open,
                    F.Id("q"), Semi, F.Id("x"), Comma,
                    F.Id("y"), Close, Sp, Plus, Sp,
                    DeltaLower, Underscore, Grp(F.Id("M")), Open,
                    F.Id("r"), Semi, F.Id("q"), Thin,
                    F.Id("x"), Comma, F.Id("q"), Thin, F.Id("y"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For source, intermediate, and target dissimilarity measures, "
                            + "define each defect as the strict source value minus the "
                            + "target value after applying its map.")),
                    Paragraph(Text(
                        "For X to Y to Z, substituting the definitions makes the middle "
                            + "measure cancel. The result is exactly sub_add_sub_cancel, "
                            + "with no metric or regularity assumptions."))),
                DescribeRole.Theorem))));
}
