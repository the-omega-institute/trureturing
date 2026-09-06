using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class FiniteMoorePenroseInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.";
    private static readonly LibraryNoteRef Penrose =
        LibraryNoteRef.Create("D5/L/Analytic/penrose1955generalized");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula MP => Seq(Operatorname, Grp(F.Id("MP")), Open, A, Close);
    private static Formula Adj(Formula x) => Seq(Open, x, Close, Caret, Grp(Star));
    private static Formula Laws(Formula inverse) => Seq(
        A, inverse, A, Sp, Eq, Sp, A, Sp, Land, Sp,
        inverse, A, inverse, Sp, Eq, Sp, inverse, Sp, Land, Sp,
        Adj(Seq(A, inverse)), Sp, Eq, Sp, A, inverse, Sp, Land, Sp,
        Adj(Seq(inverse, A)), Sp, Eq, Sp, inverse, A);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constructed finite Moore-Penrose inverse obeys all four equations and is unique.",
        H("Finite Moore-Penrose Inverse"),
        Blocks(
            Paragraph(Text(
                "For every RCLike scalar field k and finite-dimensional inner-product spaces "
                + "E and F over k, A is a linear map E to F. MP(A) is the finite sum of "
                + "rank-one maps formed from a right singular basis, weighted by inverse "
                + "squared singular values; a zero singular value contributes zero. "
                + "Products below are compositions, and star is the adjoint.")),
            Describe.Lean(
                DescribeId.Create("finite-moore-penrose-four-laws"),
                DeclarationHandle.Create(Prefix + "isMoorePenroseInverse_moorePenroseInverse"),
                H("Four derived Penrose equations"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, A, Colon, F.Id("E"), To, Underscore, Grp(F.Id("k")),
                    F.Id("F"), Comma, Sp, Laws(MP)))),
                AssessedProvenance.FromLiterature(Penrose),
                Blocks(Paragraph(Text(
                    "All four conditions are proved from the spectral construction. "
                    + "They are not hypotheses of the constructed inverse. This is an "
                    + "attributed source port of the Kitware formal owner at commit "
                    + "20461e477e1ae464d6abac1dade3188c29109b8c, with pinned-Lean "
                    + "compatibility edits and the complete upstream license retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-moore-penrose-uniqueness"),
                DeclarationHandle.Create(Prefix + "eq_moorePenroseInverse_of_isMoorePenroseInverse"),
                H("Uniqueness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, A, Colon, F.Id("E"), To, Underscore, Grp(F.Id("k")),
                    F.Id("F"), Comma, Sp, B, Colon, F.Id("F"), To, Underscore,
                    Grp(F.Id("k")), F.Id("E"), Comma, Sp,
                    Open, Laws(B), Close, Sp, Rightarrow, Sp, B, Sp, Eq, Sp, MP))),
                AssessedProvenance.FromLiterature(Penrose),
                Blocks(Paragraph(Text(
                    "Any inverse satisfying the four displayed conditions equals the "
                    + "constructed inverse. The downstream finite-synthesis bridge uses "
                    + "this to identify the ordinary inverse in the invertible case."))),
                DescribeRole.Theorem))));
}
