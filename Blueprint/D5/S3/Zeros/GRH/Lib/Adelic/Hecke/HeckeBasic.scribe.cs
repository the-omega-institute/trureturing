using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Hecke;

internal sealed class HeckeBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Basic", H("Hecke Basic"),
        Blocks(
            Paragraph(Text("Abstract Hecke operators of (G,K): coset sums, functoriality, composition as convolution.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Hecke/HeckeBasic.heckeFun_heckeFun"),
                H("heckeFun_heckeFun"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let f, f' be nonzero at finitely many representatives of G/K, f right K-invariant, v fixed by K. Then f'(fv) = (f' ∗ f)v for the action heckeFun, where (f' ∗ f)(x) = ∑ f'(g)f(g⁻¹x) over the representatives g.")))))));
}
