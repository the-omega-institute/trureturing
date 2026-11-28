using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms;

internal sealed class SingularFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular Forms", H("Singular Forms"),
        Blocks(
            Paragraph(Text("Adapted hyperbolic splittings compose, reindex and factor in stages. Coefficient at a degenerate index; definition of invariance under the radical at split places. Fourier expansion along a larger isotropic space; coefficient vanishes with singular-index ones. Singular forms: coefficients vanish if unimodular ones do, by induction on lattice index.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms.freitag"),
                H("freitag"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("After Freitag: let f be automorphic, fixed by integral points on S, with Space.Splitting.RadicalInvariant along an extra line; det T ≠ 0. If its T-coefficient vanishes at points acting on the frame by γ on S with δ⁻¹γᴴTγ unimodular, it vanishes at all points supported on S ∪ S̄.")))))));
}
