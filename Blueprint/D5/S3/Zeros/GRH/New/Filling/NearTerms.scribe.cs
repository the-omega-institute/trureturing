using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class NearTermsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Near Terms", H("Near Terms"),
        Blocks(
            Paragraph(Text("Siegel's lemma for hermitian lattices; convergence of height zeta function of subspaces. Unipotent strong approximation, and its use with freeness on the filling data. Norm identity for frames, integrality and size of minors of near terms, numerics.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/NearTerms.mem_besselS_iff_frameImage"),
                H("mem_besselS_iff_frameImage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("An isometry s lies in the Bessel subgroup S if and only if, for every vector f_a of the frame (e₁, …, e_ϱ, z), the difference s f_a − f_a lies in the span of the earlier frame vectors.")))))));
}
