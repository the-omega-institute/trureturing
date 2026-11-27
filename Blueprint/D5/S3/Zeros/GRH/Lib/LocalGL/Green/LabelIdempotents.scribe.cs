using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class LabelIdempotentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Idempotents", H("Label Idempotents"),
        Blocks(
            Paragraph(Text("Twisting a Green character by a determinant character scales the label's roots. Label idempotents are orthogonal projections; they kill twisted sums over hyperplane-fixing elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/LabelIdempotents.isCentralProj_sum_tupleIdem"),
                H("isCentralProj_sum_tupleIdem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For every finite set s of tuples (c_w) of polynomials over the finite fields k_w, the sum over s of the idempotents ⨂_w e_{c_w} is a central idempotent of the complex group algebra of ∏_w GL_n(k_w).")))))));
}
