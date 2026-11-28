using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.CongruenceRelation;

internal sealed class CongruenceStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Congruence Step", H("Congruence Step"),
        Blocks(
            Paragraph(Text("Frobenius-twisted reduced Hecke neighbours of A depend only on A + W, some W ≠ 0.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/CongruenceStep.congruence_step"),
                H("congruence_step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let β = (1 + √−d₀)/2, let z and its Hecke neighbours z·g_A (A ⊆ k_wⁿ a subspace) have V-points s, α(A), and let V → k be onto an algebraically closed field, with s reducing above a safe, good split place w of norm q. Then for some subspace W ≠ 0, Frob_q^{n−dim A} of the reduction of α(A) depends only on A + W.")))))));
}
