using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class TightFrameExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tight Frame Exists", H("Tight Frame Exists"),
        Blocks(
            Paragraph(Text("For each prime p, tight frames of every large length with a vector v such that every s₁·conj τ(v) is a p-adic unit, s₁ = Parameters.periodFactor.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/TightFrameExists.exists_isTightFrame"),
                H("exists_isTightFrame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Tight frames: for m ≥ (dN₁)⁶(R + 1) and ι: ℂ → ℂ_p there is a finite tight frame (v_i) of length m with multiplicities c_i ≥ R (IsTightFrame) in which, for some i, ι(s₁·conj τ(v_i)) is a p-adic unit at every place τ; s₁ = Parameters.periodFactor.")))))));
}
