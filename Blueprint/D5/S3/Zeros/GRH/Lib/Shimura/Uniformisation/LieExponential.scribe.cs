using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class LieExponentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lie Exponential", H("Lie Exponential"),
        Blocks(
            Paragraph(Text("Theta functions on complex tori, Riemann form, semicharacters, Heisenberg translations, basic API. Exponential map of a compact commutative complex Lie group has lattice kernel.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/LieExponential.exists_lie_exponential"),
                H("exists_lie_exponential"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Exponential map: a compact abelian group G with a chart at 0 in V in which addition is analytic has a homomorphism e : V → G, analytic at 0 with derivative 1, image of finite index, kernel a lattice; homomorphisms from complex spaces, continuous and differentiable at 0, factor linearly through e.")))))));
}
