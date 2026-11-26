using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class KroneckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kronecker", H("Kronecker"),
        Blocks(
            Paragraph(Text("The Kronecker product map U(S)×U(T) → unitary group of Hom(S,T).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/Kronecker.kron"),
                H("kron"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For SK = 1 and J = T ⊗ Kᵀ, the homomorphism (g, h) ↦ h ⊗ (g⁻¹)ᵀ from U(S) × U(T) to U(J): the action x ↦ hxg⁻¹ on matrices.")))))));
}
