using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class FockThetaFunctionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Theta Functions", H("Fock Theta Functions"),
        Blocks(
            Paragraph(Text("Entire canonical theta functions come from finite Weil vectors, with Schur orthogonality.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/FockThetaFunctions.exists_entireTheta_eq"),
                H("exists_entireTheta_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V be standard, d in E integral, d d̄ = N ≠ 0. An entire S fixed by the normalised translations by −realImage(d̄γ), for all γ with α⁻¹γ integral, is Θ_F for some F in 𝒲_f that has orthogonality data Space.VacuumExpansion for d, N.")))))));
}
