using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RibetCramerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ribet Cramer", H("Ribet Cramer"),
        Blocks(
            Paragraph(Text("Ribet's operator by Cramer's rule twice; normalising element; Amitsur for families.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RibetCramer.exists_ribet_element_cramer"),
                H("exists_ribet_element_cramer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Ribet's construction for representations u_x of O[G] with characteristic polynomials over S. Let the O[G]-linear form V send the rows of M into 𝔞·V(w) plus the left ideal of r with all tr u(rg) ∈ 𝒥. Some f ∈ S equals det u_x(M)·tr u_x(h) where u_x(𝔞h) = 0, and f·det u(V(w)) ∈ 𝒥.")))))));
}
