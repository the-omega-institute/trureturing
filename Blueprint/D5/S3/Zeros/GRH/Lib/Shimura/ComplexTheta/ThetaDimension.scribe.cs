using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ComplexTheta;

internal sealed class ThetaDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Dimension", H("Theta Dimension"),
        Blocks(
            Paragraph(Text("Theta series converge; Frobenius dimension formula, irreducibility and Schur's lemma for the theta group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/ThetaDimension.schur_lemma"),
                H("schur_lemma"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Schur's lemma: for Appell–Humbert data with positive Riemann form, an endomorphism of the space of theta functions that commutes with the twisted translations by the dual lattice is a scalar.")))))));
}
