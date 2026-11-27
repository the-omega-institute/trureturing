using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline;

internal sealed class CrystallineClassesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Classes", H("Crystalline Classes"),
        Blocks(
            Paragraph(Text("Crystalline comparison on charts étale over tori, by adjoining roots of coordinates. Čech–Alexander flat base change; crystalline classes span period-ring cohomology.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineClasses.span_range_crysComparison_pull_eq_top"),
                H("span_range_crysComparison_pull_eq_top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be a p-complete DVR, uniformiser p, r: R → S/𝔡(S) compatible with O_C → A_max/𝔡, V as in IsCharting. If the period cohomology of V on p-adic tests is finite over B_max, restrictions from H^n(V(D/𝔡), D), D over S, span it.")))))));
}
