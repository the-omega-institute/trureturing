using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class JetDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jet Divisibility", H("Jet Divisibility"),
        Blocks(
            Paragraph(Text("Tilting matrices that kill Frobenius pairings at controlled determinant cost. Lower bound for valuations of Schur jets when Frobenius couplings are silenced.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/JetDivisibility.norm_schurJet_le"),
                H("norm_schurJet_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Divisibility of Schur jets. Let κ fit, with B boxes, |ϖ| = p^{−ρ}, |θ| = p^ω, and let the charges g be nonzero at one end of each coupling exempted by the even places ev. If IsIntegralOnNullCone holds up to degree B, each entry of the jet matrix along S_κ has valuation ≥ (1/(p−1) − ρ)B + ω∑couplingCount − |Φ||n′|³(⌊log_p B⌋ + 1) − m, m the total charge of the boxes of its row.")))))));
}
