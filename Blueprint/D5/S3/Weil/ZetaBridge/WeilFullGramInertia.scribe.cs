using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilFullGramInertiaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilFullGramInertia.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual full mixed Weil Gram is Hermitian and represents synthesized full zero sums; a constructed common Burnol family has exact spectral negative index equal to its observable orbit dimension.",
        H("Actual Full Weil Gram Inertia"),
        Blocks(
            Describe.Lean(DescribeId.Create("full-weil-gram-hermitian"),
                DeclarationHandle.Create(Prefix + "fullWeilGram_isHermitian"),
                H("Hermitian symmetry by actual zero reindexing"),
                StatementSource.FromAuthor(Disp(F.Id("G(i,j) = W(basis(j),basis(i)); conjugateTranspose(G) = G"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entries are absolutely convergent mixed zero sums. Conjugation swaps the tests after the existing multiplicity-preserving mirror permutation. The row convention is conjugate-linear."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-weil-gram-exact-quadratic"),
                DeclarationHandle.Create(Prefix + "fullWeilGram_quadratic"),
                H("Exact full form, including every cross term"),
                StatementSource.FromAuthor(Disp(F.Id("star(a) dot (G mulVec a) = actual full zeroSum of the synthesized convolution square"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mixed summability justifies moving finite coefficient sums through the complete zero sum. This identifies a concrete full Gram, with no substituted scalar matrix or discarded tail."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-weil-gram-exact-negative-index"),
                DeclarationHandle.Create(Prefix + "exists_actual_full_weil_gram_with_exact_negative_index"),
                H("Full spectral inertia of the realized observable family"),
                StatementSource.FromAuthor(Disp(F.Id("exists actual basis with injective synthesis, PosDef(-G), and RHLinalg.negIndex(G) = card(orbit channels)"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing common Burnol construction supplies the basis and coefficient-uniform full negativity. Standard positive-definite matrix spectral facts then compute the repository negative index.")),
                    Paragraph(Text("A valid finite separated nonreal off-line orbit frame remains an input. No existence of off-line zeros, RH, equality with ambient multiplicity-expanded index, or global fixed support bound is asserted. Source completion remains Candidate until pinned replay and axiom/admission checks."))),
                DescribeRole.Theorem)), []));
}
