using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Weil;

internal sealed class FockCoeffDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Coeff Decay", H("Fock Coeff Decay"),
        Blocks(
            Paragraph(Text("Explicit degree-uniform decay of Heisenberg matrix coefficients of homogeneous Fock vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Weil/FockCoeffDecay.norm_realInner_realHeisOp_le"),
                H("norm_realInner_realHeisOp_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P be homogeneous of degree d in |ι| > 0 variables, v = v_P, σ in U(ε), A ≥ d + |ι| and n natural numbers, y ≠ 0. Then |⟨v, ϱ(y)ω(σ)v⟩| ≤ (4(A+n))^n |y|^{−2n} ‖σ‖^{|ι|+2n} ⟨v,v⟩, with Euclidean and ℓ² operator norms.")))))));
}
