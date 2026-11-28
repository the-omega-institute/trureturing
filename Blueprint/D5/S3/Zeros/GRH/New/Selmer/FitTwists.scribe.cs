using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class FitTwistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fit Twists", H("Fit Twists"),
        Blocks(
            Paragraph(Text("Adjoint of the Hecke polynomial operator in each Galois-conjugate Petersson product. Projecting tested forms to lifts does not increase any conjugate norm. Hecke algebra off the level, eigenspaces and their projections on the proof's spaces. Auxiliary theta descent as a map of forms, its equivariance and adjoint. Spaces of lifts, ramified and rank-one pairs, budget; what a good twist family satisfies.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/FitTwists.exists_theta_to_principalForms"),
                H("exists_theta_to_principalForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For each j there is a ℂ-linear map from the forms on V_j to the forms of principal level g on W_j which, when 1 ≤ j ≤ m, sends Ξ to the auxiliary theta lift θ_jΞ.")))))));
}
