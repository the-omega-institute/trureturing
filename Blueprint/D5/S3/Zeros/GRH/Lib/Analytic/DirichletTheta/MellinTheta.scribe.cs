using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Analytic.DirichletTheta;

internal sealed class MellinThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mellin Theta", H("Mellin Theta"),
        Blocks(
            Paragraph(Text("Gaussian theta series of a character: Poisson symmetry, Mellin transform is Gamma times L.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Analytic/DirichletTheta/MellinTheta.thetaTailIntegral_zero_le_two_mul"),
                H("thetaTailIntegral_zero_le_two_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For j ≤ 1, primitive non-principal χ mod q with χ(−1) = (−1)^j, T > 0 and q ≤ T²: ∫_0^∞ |θ(t)| dt/√t ≤ 2 ∫_{1/T}^∞ |θ(t)| dt/√t, where θ = gaussianTheta j χ.")))))));
}
