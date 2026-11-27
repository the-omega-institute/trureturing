using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Primitive;

internal sealed class TiltedTheoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tilted Theory", H("Tilted Theory"),
        Blocks(
            Paragraph(Text("Comparison map from F_p to the tilt; tilted coefficients form a theory with supports.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/TiltedTheory.tiltTheory"),
                H("tiltTheory"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The theory (ℓ = p) on p-adic tests along R ↦ R[1/p] with coefficient R^♭ ⊗ M over O^♭, assuming the coefficient satisfies IsAcyclicOnPerfect (acyclicity on every perfect O^♭-algebra).")))))));
}
