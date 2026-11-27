using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class CrystallinePeriodMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Period Matrix", H("Crystalline Period Matrix"),
        Blocks(
            Paragraph(Text("Period matrix of a crystalline lattice with Frobenius matrix and Hodge basis.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/CrystallinePeriodMatrix.exists_isPeriodMatrix"),
                H("exists_isPeriodMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j(Γ) contain the fixer of Λ and θ(z), T be crystalline with basis e and jumps in [−a, b]. There are an invertible M over B with invariant columns and a unit v of A_inf, Eτv = μ, with U = (Eτ)^aM a period matrix over B^+ for (a + b, v^a).")))))));
}
