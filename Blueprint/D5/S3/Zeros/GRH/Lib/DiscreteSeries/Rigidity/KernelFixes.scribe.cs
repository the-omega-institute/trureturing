using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity;

internal sealed class KernelFixesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel Fixes", H("Kernel Fixes"),
        Blocks(
            Paragraph(Text("Discrete series projector on representations: idempotent, fixes highest vectors, positivity, kills other K-types.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/KernelFixes.eq_casimirValue_of_ge"),
                H("eq_casimirValue_of_ge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Rigidity: let ρ differentiate π (IsUnitaryRep) along ι, l = 2λ have gap 500n³ + A, v be K-highest of weight Λ, and ι(Ωv) = c·ιv for the full Casimir Ω. If c ≥ c(λ) and ιv ≠ 0, then c = c(λ).")))))));
}
