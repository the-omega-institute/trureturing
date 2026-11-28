using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class ModularDataDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Modular Data Decay", H("Modular Data Decay"),
        Blocks(
            Paragraph(Text("Operator norm of block diagonal matrices; block embeddings are proper maps. Rapid decay of theta kernels for data mod m supported on full-rank matrices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/ModularDataDecay.pairTheta_modDatum_decay"),
                H("pairTheta_modDatum_decay"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let 𝔪 ≠ (1), Ψ be supported on left invertible matrices mod 𝔪, and θ the kernel of v ⊗ Ψ. For each M there are B, N, C with |θ(g,h)| ht(g)^M ≤ C mom_N(v) ht(h)^B for all g, h and all v with finite N-th moment.")))))));
}
