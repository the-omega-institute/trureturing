using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class ResidualIrreducibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual Irreducibility", H("Residual Irreducibility"),
        Blocks(
            Paragraph(Text("Tame pair with residually distinct conjugate eigenvalues spans all matrices of a lattice.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/ResidualIrreducibility.span_eq_top_of_tame_pair"),
                H("span_eq_top_of_tame_pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let u be an O-lattice for R of rank n, R(γ^q) = R(φ⁻¹γφ), R(γ^{qⁿ}) = R(γ), and ζ ∈ O an eigenvalue of R(γ) with ζ^{q^i} (i < n) residually distinct. Then u(G) spans all matrices over O and u(φ^{−n}) is scalar.")))))));
}
