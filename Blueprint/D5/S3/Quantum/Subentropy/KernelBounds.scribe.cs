using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class KernelBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical subentropy kernel has a sharp vertex-dependent integrable bound.",
        H("Classical kernel bounds"),
        Blocks(
            Describe.Lean(DescribeId.Create("classical-kernel-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/KernelBounds.classical_kernel_bounds"),
                H("A uniform bound at every probability vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("Let p be any nonnegative finite real vector whose entries sum to one. For every chosen coordinate x and every t>0, its diagonal kernel satisfies 0<=K(diag p,t)<=(1−p_x)/(1+t)^2. Zero probabilities are allowed.")),
                    Paragraph(Text("The lower bound uses the product inequality product(1+p_i/t)>=1+1/t. For the upper bound, log u<=u−1 and exp v>=1+v imply product(a_i/b_i)>=1−sum((b_i−a_i)/a_i) for strictly positive vectors a,b. Apply this at a_i=t+delta_ix and b_i=t+p_i; the sum on the right is (1−p_x)/(t(1+t)), and the vertex product is t/(1+t)."))), DescribeRole.Theorem))));
}
