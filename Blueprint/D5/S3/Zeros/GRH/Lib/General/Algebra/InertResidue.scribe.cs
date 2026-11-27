using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class InertResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inert Residue", H("Inert Residue"),
        Blocks(
            Paragraph(Text("A general count of the fixed points of an involution on a finite field, applied to finite places of a stably unramified CM field: a place with w̄ = w has norm r ^ 2 with r ≡ 3 mod 4, so a place of prime norm is split.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/InertResidue.exists_sq_eq_q_of_inert"),
                H("exists_sq_eq_q_of_inert"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For stably unramified E and a finite place w with w = w̄, the norm of w is r² for a natural number r ≡ 3 mod 4.")))))));
}
