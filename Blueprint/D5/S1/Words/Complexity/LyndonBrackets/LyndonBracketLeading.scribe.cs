using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.LyndonBrackets;

internal sealed class LyndonBracketsLyndonBracketLeadingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed standard factors have their defining Lyndon word as leading monomial.",
        H("LyndonBracketLeading"),
        Blocks(
            Paragraph(Text(
                "The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, "
                + "standard factorization, and the triangular standard-bracket construction are "
                + "classical word and free-Lie-algebra material; the cited k-deck paper points to "
                + "Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean "
                + "implementation used by the later actual-positive-word construction.")),
            D("standard-factor-closed", "StandardFactorClosed", "Recursive word-theoretic closure",
                "StandardFactorClosed is false on the empty word, true on singletons, and on longer words requires both standard factors recursively closed and the original word smaller than the reversed factor concatenation.", DescribeRole.Definition),
            D("is-lyndon-standard-factor-closed", "isLyndon_standardFactorClosed", "Lyndon words satisfy the closure",
                "Every actual Lyndon word is StandardFactorClosed throughout its recursive longest-suffix factorization.", literature: true),
            D("standard-bracket-leading-word", "standardBracket_hasLeadingWord", "The bracket is triangular",
                "For every StandardFactorClosed word w, standardBracket w has leading word w with coefficient one and no lexicographically smaller supported word.", literature: true),
            D("standard-bracket-linear-independent", "standardBracket_linearIndependent", "Standard brackets are independent",
                "Over the integers, the family w |-> standardBracket w indexed by StandardFactorClosed words is linearly independent in all degrees jointly. The proof reads the least leading word in a finite relation.", literature: true))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "StandardFactorClosed" => Seq(
            Equal(Call("StandardFactorClosed", F.Id("empty")), F.Id("False")), Land,
            Open, Forall, Sp, F.Id("a"), Comma,
            Equal(Call("StandardFactorClosed", Call("singleton", F.Id("a"))),
                F.Id("True")), Close, Land, Forall, Sp, F.Id("w"), Comma,
            F.D(2), Leq, Call("length", F.Id("w")), Rightarrow,
            Call("StandardFactorClosed", F.Id("w")), Iff,
            Call("StandardFactorClosed", Call("standardLeft", F.Id("w"))), Land,
            Call("StandardFactorClosed", Call("standardRight", F.Id("w"))), Land,
            Sp, F.Id("w"), Lt, Call("append", Call("standardRight", F.Id("w")),
                Call("standardLeft", F.Id("w")))),
        "isLyndon_standardFactorClosed" => Seq(Forall, Sp, F.Id("w"),
            Comma, Call("IsLyndon", F.Id("w")), Rightarrow,
            Call("StandardFactorClosed", F.Id("w"))),
        "standardBracket_hasLeadingWord" => Seq(Forall, Sp, F.Id("w"),
            Comma, Call("StandardFactorClosed", F.Id("w")), Rightarrow,
            Call("HasLeadingWord", Call("standardBracket", F.Id("w")), F.Id("w"))),
        "standardBracket_linearIndependent" =>
            Call("LinearIndependent", F.Id("Z"),
                Call("standardBracket", Call("StandardFactorClosedWords", F.Id("A")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
