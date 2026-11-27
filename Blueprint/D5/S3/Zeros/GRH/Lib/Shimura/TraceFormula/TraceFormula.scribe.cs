using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.TraceFormula;

internal sealed class TraceFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace Formula", H("Trace Formula"),
        Blocks(
            Paragraph(Text("Trace of a (twisted) Hecke operator on algebraic forms as sum over representatives.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/TraceFormula.trace_eq_weighted_sum"),
                H("trace_eq_weighted_sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Trace formula. M: the F : G → W with F(e(γ)g) = ρ(γ)F(g), right K-invariant, zero on D. The sets {γ : e(γ)r_iK = gK} are finite, empty for g ∈ D, with ∑_i w_i·cardinality = 1 for g ∉ D; σ⁻¹K = K; TF = a·(s∘F∘σ⁻¹), a ∈ A[G] acting by right translation. Then dim M < ∞, tr T = ∑_i w_i ∑_γ φ(r_i⁻¹σ(e(γ)r_i)) tr(sρ(γ)), φ the image of a in A[G/K].")))))));
}
