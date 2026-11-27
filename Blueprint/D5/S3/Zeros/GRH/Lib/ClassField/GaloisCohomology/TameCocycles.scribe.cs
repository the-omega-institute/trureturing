using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class TameCocyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tame Cocycles", H("Tame Cocycles"),
        Blocks(
            Paragraph(Text("Tame cocycles are determined by a tame generator and Frobenius; local length bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/TameCocycles.exists_conj_side_detects"),
                H("exists_conj_side_detects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let γ be the tame generator at A over P ∤ ℓ, ρ unramified at v = P or P̄, ℓ^M B = 0. For σ' = σ or σ^{−c}, Selmer cocycles killing γ' are unramified at v, and vanish on a decomposition group if they also kill φ', φ a Frobenius at A.")))))));
}
