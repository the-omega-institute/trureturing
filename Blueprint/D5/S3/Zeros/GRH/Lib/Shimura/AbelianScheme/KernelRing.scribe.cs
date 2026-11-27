using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme;

internal sealed class KernelRingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel Ring", H("Kernel Ring"),
        Blocks(
            Paragraph(Text("Abelian schemes with ring action, translations, Picard pairing, parallelogram law: definitions. Spec of algebras as schemes over a ring; full faithfulness. Kernel of a finite homomorphism is the spectrum of a finite algebra.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/KernelRing.exists_finite_kernel_ring"),
                H("exists_finite_kernel_ring"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let B be a separated commutative group scheme over R and f : A → B finite. The fibre of f over the zero section is represented by a closed subscheme Spec S of A, S a finite R-algebra, flat if f is flat.")))))));
}
