using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.LyndonBrackets;

internal sealed class LyndonBracketsLyndonStandardFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The longest Lyndon suffix gives the recursive standard factorization.",
        H("LyndonStandardFactorization"),
        Blocks(
            Paragraph(Text(
                "The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, "
                + "standard factorization, and the triangular standard-bracket construction are "
                + "classical word and free-Lie-algebra material; the cited k-deck paper points to "
                + "Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean "
                + "implementation used by the later actual-positive-word construction.")),
            D("standard-cut", "standardCut", "The longest-Lyndon-suffix cut",
                "For w of length at least two, standardCut w is the least positive cut index whose suffix is Lyndon; hence it selects the longest proper Lyndon suffix.", DescribeRole.Definition, true),
            D("standard-left", "standardLeft", "Standard left factor",
                "standardLeft w hw is w.take (standardCut w hw) for a word whose length is at least two.", DescribeRole.Definition, true),
            D("standard-right", "standardRight", "Standard right factor",
                "standardRight w hw is w.drop (standardCut w hw), the longest proper Lyndon suffix.", DescribeRole.Definition, true),
            D("is-lyndon-standard-left", "isLyndon_standardLeft", "The left factor remains Lyndon",
                "If w is Lyndon and has length at least two, then its standardLeft factor is Lyndon.", literature: true))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
