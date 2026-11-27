using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.GaussSum;

internal sealed class LocalHomUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Hom Unit", H("Local Hom Unit"),
        Blocks(
            Paragraph(Text("Finite Fourier inversion on matrices; Gauss sums of primitive determinant characters. GL_n transitive on unimodular vectors, index of stabiliser; iterated composition of maps. Iterated tensor products, pure tensors, multilinear extension of a composite of maps. Local ring homomorphisms reflect invertibility of matrices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/GaussSum/LocalHomUnit.liftInPairs_pure"),
                H("liftInPairs_pure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The composite of the first p double steps (TensorChain.liftInPairs) at the pure tensors f_{2i} ⊗ f_{2i+1} agrees at every x with the composite of the first 2p single steps b_j(f_j).")))))));
}
