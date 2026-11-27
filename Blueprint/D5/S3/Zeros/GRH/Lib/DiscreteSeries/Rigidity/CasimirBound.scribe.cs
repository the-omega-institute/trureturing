using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity;

internal sealed class CasimirBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Casimir Bound", H("Casimir Bound"),
        Blocks(
            Paragraph(Text("Invariant forms, compact Casimir value, words and filtration of a (g,K)-module. Commutation rules, Casimir invariance and filtration basics for gl_n-modules. Arithmetic of rho, lowest K-type and gap of a Harish-Chandra parameter. Casimir value on K-highest vectors and resulting Parthasarathy-type inequality on weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/CasimirBound.casimir_bound"),
                H("casimir_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l = 2λ have some gap and let IsUnitaryCasimirGe hold (invariant inner product, Ω ≥ |λ|² − |ρ|²). If x ≠ 0 is K-highest of weight Λ + ν, then |ν|² + 2⟨ν, λ⟩ ≥ −n³.")))))));
}
