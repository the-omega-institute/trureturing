using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.LocalHeight;

internal sealed class EulerAdditionFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler Addition Formula", H("Euler Addition Formula"),
        Blocks(
            Paragraph(Text("Integral series in the formal parameter along linear forms; Euler's addition formula.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/LocalHeight/EulerAdditionFormula.translatedWpDeriv_add_mem_multiPhiRing"),
                H("translatedWpDeriv_add_mem_multiPhiRing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Euler's addition formula, integral form: read in ℂ_p, the series φ(u + w) lies in 𝔬[[φ(u), φ(w)]].")))))));
}
