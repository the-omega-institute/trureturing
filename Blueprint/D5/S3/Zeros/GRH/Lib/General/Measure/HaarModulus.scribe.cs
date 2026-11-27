using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Measure;

internal sealed class HaarModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Haar Modulus", H("Haar Modulus"),
        Blocks(
            Paragraph(Text("Haar measure push-forwards, modulus versus index, modulus of GL_n equals modulus of determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Measure/HaarModulus.distribHaarChar_GL_eq_det"),
                H("distribHaarChar_GL_eq_det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let R be a locally compact Polish commutative ring with a compact open subring O satisfying IsValuationPair. Then g in GL_n(R) scales Haar measure on R^n by the same factor as det g scales Haar measure on R.")))))));
}
