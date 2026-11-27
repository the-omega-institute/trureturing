using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class TwistedTraceSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twisted Trace Sum", H("Twisted Trace Sum"),
        Blocks(
            Paragraph(Text("Level decomposition and commuting families of local and spherical operators for the trace comparison. Twisted trace of Hecke operator on definite unitary group as weighted orbital sum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/TwistedTraceSum.isSampleTotal_twisted_trace"),
                H("isSampleTotal_twisted_trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Twisted trace formula on definite V: for compatible σ, τ, s and open σ-stable L ≤ K ≤ K_0, some c ≠ 0 makes the trace on L-fixed forms of the Hecke operator of φ times ψ ↦ s∘ψ∘σ⁻¹ a sample sum (IsSampleTotal) of weight c of φ(x⁻¹γσ(x)) tr(ρ(γ)s).")))))));
}
