using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.TaylorWiles;

internal sealed class AuxPlaceOperatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aux Place Operators", H("Aux Place Operators"),
        Blocks(
            Paragraph(Text("Finite groups at auxiliary places act on forms; Higman operator up to stabiliser orders.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/AuxPlaceOperators.exists_higman_operator"),
                H("exists_higman_operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Higman's criterion up to c: for a finite group Δ embedded by φ in ∏_j GL_n(k_{w_j}), some lattice-preserving operator Ψ on forms of principal level has ∑_{g∈Δ} g⁻¹Ψg = c, a common multiple of the stabiliser orders.")))))));
}
