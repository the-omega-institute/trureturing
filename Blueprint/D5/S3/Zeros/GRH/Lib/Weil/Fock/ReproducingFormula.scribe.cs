using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class ReproducingFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reproducing Formula", H("Reproducing Formula"),
        Blocks(
            Paragraph(Text("Reproducing formula by theta lifts to large definite groups; holomorphic determinant vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/ReproducingFormula.reproducing_formula_modKernel"),
                H("reproducing_formula_modKernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Reproducing formula. Let 2n < n′, 𝔪 = (N) ≠ (1), c, b unramified, Q₀ ≠ 0 holomorphic of dominant weight u, m = holMinorsPi s u integrable, Q spanning the U(n′)(ℝ)-translates of Q₀ at each class. For each x, ψ ↦ ∫ψ(xh)m(h)dh on rapid level-N ψ combines the pairings with θ^{S,I_{n′}}_{c,b}[1_e,Q] linearly.")))))));
}
