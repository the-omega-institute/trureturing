using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class KernelDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel Decay", H("Kernel Decay"),
        Blocks(
            Paragraph(Text("Rapid decay of theta kernels for data supported on full-rank maps at split places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/KernelDecay.pairTheta_decay_of_onto"),
                H("pairTheta_decay_of_onto"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P ∩ P̄ = ∅, Ψ Schwartz–Bruhat above P, supported on matrices right invertible after a ring map φ: 𝔸_f → R ≠ 0. Each N has B, M, C with |θ_{a,b}(v⊗Ψ⊗vac)(g,h)|·ht(h)^N ≤ C·mom_M(v)·ht(g)^B for all g, h and v with mom_M(v) finite.")))))));
}
