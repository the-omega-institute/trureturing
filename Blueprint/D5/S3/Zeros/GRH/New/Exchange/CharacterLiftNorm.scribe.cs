using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class CharacterLiftNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character Lift Norm", H("Character Lift Norm"),
        Blocks(
            Paragraph(Text("Norm of the adjoint lift from W_j: twist-free constant, explicit count, Hecke sum. Squared norm of the theta lift from U(1) is a Hecke L-value.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/CharacterLiftNorm.inner_trivialLift_self_eq_L"),
                H("inner_trivialLift_self_eq_L"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For even rank n ≥ 4, ⟨Ξ, Ξ⟩ = C·hookNumber·d·L^S(n/2, μ⁻¹)·(∏_{w ∈ Q} Nw)^{n−1}, where d is the dimension of the weight, S the set of the places of M and Q, and C ≠ 0 depends on X only through the places of M.")))))));
}
