using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class UnipotentCovolumeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unipotent Covolume", H("Unipotent Covolume"),
        Blocks(
            Paragraph(Text("Explicit covolume of the level-g arithmetic unipotent group in scaled real coordinates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/UnipotentCovolume.lintegral_classCutoff_eq_unipCovolume"),
                H("lintegral_classCutoff_eq_unipCovolume"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Under the standing hypotheses, for every class c and archimedean point y, the integral of the cutoff β_c(uy) over u in 𝖴_∞, for the product Haar measure, equals the covolume ν, which does not depend on c.")))))));
}
