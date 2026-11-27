using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class LinkPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Link Pairing", H("Link Pairing"),
        Blocks(
            Paragraph(Text("Bordered determinant bounds the discriminant of the lattice of lifts of a link. Discriminant gain for congruent terms with differing links, via lattices of lifts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/LinkPairing.pairInvariant_mul_le"),
                H("pairInvariant_mul_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For γ, γ' of level j over one agreeing s with Filling.FixesNormAtLeast s x, some i has |κ| ≤ dim T° + i + (j−ϱ)₊ (T° = commonLink γ γ'), is 0 only for equal links, and P(γ,γ')P(γ',γ)x'² ≤ (2/g)^(2if)·G(γ)G(γ') (P = Filling.pairInvariant, G = Filling.classGauge j c c'); x' = x if j > ϱ and i = 0, else 1.")))))));
}
