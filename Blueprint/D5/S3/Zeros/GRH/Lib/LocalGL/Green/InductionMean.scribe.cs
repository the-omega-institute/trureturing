using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class InductionMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induction Mean", H("Induction Mean"),
        Blocks(
            Paragraph(Text("Frobenius reciprocity between parabolic induction and block means on GL_n(F_q).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/InductionMean.rankInner_mul_eq_sum_skew"),
                H("rankInner_mul_eq_sum_skew"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Frobenius reciprocity for the induction product over a finite field k: the rank n pairing ⟨A∗B, X⟩ equals the sum over i + j = n of the rank i pairings of A with Hall.skew j B X.")))))));
}
