using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class ThetaIntegralLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Integral Laws", H("Theta Integral Laws"),
        Blocks(
            Paragraph(Text("Name for the real slice of a datum in the mixed model. Real part of the slice at an isotropic line in the constant term. Basic laws of theta integrals: equivariance, linearity, automorphy, boundedness for full-rank data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/ThetaIntegralLaws.IsTargetBounded"),
                H("IsTargetBounded"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("There are B and C with |θ^{S,T}_{α,β}(f)(g,h)| ≤ C·ht(g)^B for all characters α, β and all g, h: polynomial growth in g, uniformly in h.")))))));
}
