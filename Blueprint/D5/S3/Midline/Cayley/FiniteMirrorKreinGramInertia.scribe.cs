using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class FiniteMirrorKreinGramInertiaDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/FiniteMirrorKreinGramInertia.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual mirror-Krein Gram matrix of the finite odd basis is minus two times identity and has exact negative index kappa_T.",
            H("Finite mirror Krein Gram inertia"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-mirror-krein-gram-is-negative-identity"),
                    DeclarationHandle.Create(Module + "finiteMirrorOddKreinGram_eq"),
                    H("The actual odd Gram matrix is -2 I"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("G_T^-"), Sp, EqualTo, Sp, F.Id("-2 I")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The matrix entries are computed from genuine odd vectors inside the multiplicity-expanded zero Hilbert space and the actual mirror Krein form."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-mirror-krein-gram-negative-index"),
                    DeclarationHandle.Create(Module + "finiteMirrorOddKreinGram_negIndex"),
                    H("The actual Gram negative index equals the mirror-orbit multiplicity count"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("negIndex", F.Id("G_T^-")), Sp, EqualTo, Sp,
                        F.Id("kappa_T")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is a spectral inertia theorem for a concrete Hermitian Gram matrix, not a definition of an abstract negative dimension."))),
                    DescribeRole.Theorem))));
    }
}
