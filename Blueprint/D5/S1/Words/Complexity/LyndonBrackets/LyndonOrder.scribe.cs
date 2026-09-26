using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.LyndonBrackets;

internal sealed class LyndonBracketsLyndonOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lyndon words are ordered by their proper suffixes and admit Lyndon concatenation.",
        H("LyndonOrder"),
        Blocks(
            Paragraph(Text(
                "The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, "
                + "standard factorization, and the triangular standard-bracket construction are "
                + "classical word and free-Lie-algebra material; the cited k-deck paper points to "
                + "Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean "
                + "implementation used by the later actual-positive-word construction.")),
            D("is-lyndon", "IsLyndon", "Rotation-minimal Lyndon words",
                "For w : List A, IsLyndon w means w is nonempty and, for every factorization w=u++v with u and v nonempty, w is strictly lexicographically smaller than v++u.", DescribeRole.Definition, true),
            D("is-lyndon-iff-suffix", "isLyndon_iff_lt_suffix", "Suffix characterization",
                "For every word w, IsLyndon w is equivalent to w being nonempty and strictly smaller than every nonempty proper suffix v of w.", literature: true),
            D("is-lyndon-append", "isLyndon_append", "Increasing concatenation is Lyndon",
                "If u and v are Lyndon and u<v in list lexicographic order, then u++v is Lyndon.", literature: true),
            D("exists-lyndon-suffix-cut", "exists_lyndon_suffix_cut", "A proper Lyndon suffix exists",
                "For every w with 2<=w.length, there is i with 0<i<w.length such that w.drop i is Lyndon.", literature: true))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "IsLyndon" => Seq(Forall, Sp, F.Id("w"), Comma, Sp,
            Call("IsLyndon", F.Id("w")), Iff, Sp, F.Id("w"), Neq,
            Sp, F.Id("empty"),
            Land, Forall, Sp, F.Id("u"), Comma, F.Id("v"), Comma,
            F.Id("u"), Neq, Sp, F.Id("empty"), Land, Sp, F.Id("v"), Neq,
            Sp, F.Id("empty"),
            Land, Sp, Equal(F.Id("w"), Call("append", F.Id("u"), F.Id("v"))),
            Rightarrow, Sp, F.Id("w"), Lt,
            Call("append", F.Id("v"), F.Id("u"))),
        "isLyndon_iff_lt_suffix" => Seq(Forall, Sp, F.Id("w"), Comma,
            Call("IsLyndon", F.Id("w")), Iff, Sp, F.Id("w"), Neq,
            Sp, F.Id("empty"),
            Land, Forall, Sp, F.Id("v"), Comma, F.Id("v"), Neq,
            Sp, F.Id("empty"),
            Land, Call("ProperSuffix", F.Id("v"), F.Id("w")), Rightarrow,
            Sp, F.Id("w"), Lt, Sp, F.Id("v")),
        "isLyndon_append" => Seq(Forall, Sp, F.Id("u"), Comma,
            F.Id("v"), Comma, Call("IsLyndon", F.Id("u")), Land,
            Call("IsLyndon", F.Id("v")), Land, Sp, F.Id("u"), Lt,
            Sp, F.Id("v"),
            Rightarrow, Call("IsLyndon", Call("append", F.Id("u"), F.Id("v")))),
        "exists_lyndon_suffix_cut" => Seq(Forall, Sp, F.Id("w"), Comma,
            F.D(2), Leq, Call("length", F.Id("w")), Rightarrow, Exists, Sp,
            F.Id("i"), Comma, F.D(0), Lt, Sp, F.Id("i"), Lt,
            Call("length", F.Id("w")), Land,
            Call("IsLyndon", Call("drop", F.Id("w"), F.Id("i")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
