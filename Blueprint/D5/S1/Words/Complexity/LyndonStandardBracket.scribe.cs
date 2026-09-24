using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class LyndonStandardBracketDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonStandardBracket";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lyndon words admit longest-suffix standard factorization, and their recursive integral brackets have triangular leading words and are linearly independent.",
        H("Lyndon Standard Brackets and Leading Words"),
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
                "For every w with 2<=w.length, there is i with 0<i<w.length such that w.drop i is Lyndon.", literature: true),
            D("standard-cut", "standardCut", "The longest-Lyndon-suffix cut",
                "For w of length at least two, standardCut w is the least positive cut index whose suffix is Lyndon; hence it selects the longest proper Lyndon suffix.", DescribeRole.Definition, true),
            D("standard-left", "standardLeft", "Standard left factor",
                "standardLeft w hw is w.take (standardCut w hw) for a word whose length is at least two.", DescribeRole.Definition, true),
            D("standard-right", "standardRight", "Standard right factor",
                "standardRight w hw is w.drop (standardCut w hw), the longest proper Lyndon suffix.", DescribeRole.Definition, true),
            D("is-lyndon-standard-left", "isLyndon_standardLeft", "The left factor remains Lyndon",
                "If w is Lyndon and has length at least two, then its standardLeft factor is Lyndon.", literature: true),
            D("word-polynomial", "WordPolynomial", "Integral word algebra",
                "WordPolynomial A abbreviates MonoidAlgebra Z (FreeMonoid A), so monomials are finite words and coefficients are integers.", DescribeRole.Definition, true),
            D("word-monomial", "wordMonomial", "A word basis monomial",
                "wordMonomial w is the monoid-algebra singleton at FreeMonoid.ofList w with coefficient one.", DescribeRole.Definition),
            D("homogeneous", "Homogeneous", "Homogeneous word polynomials",
                "Homogeneous p n means every monomial in the coefficient support of p has free-monoid length n.", DescribeRole.Definition),
            D("has-leading-word", "HasLeadingWord", "Triangular leading word",
                "HasLeadingWord p w requires p homogeneous of degree w.length, coefficient one at w, and every supported word lexicographically at least w.", DescribeRole.Definition),
            D("commutator", "commutator", "The word-algebra commutator",
                "commutator p q is p*q-q*p in the integral noncommutative word algebra.", DescribeRole.Definition, true),
            D("standard-bracket", "standardBracket", "Recursive standard bracketing",
                "The empty word maps to zero, a singleton maps to its basis monomial, and a longer word maps to the commutator of the recursively bracketed standardLeft and standardRight factors.", DescribeRole.Definition, true),
            D("standard-bracket-homogeneous", "standardBracket_homogeneous", "Standard brackets preserve length",
                "For every word w, standardBracket w is homogeneous of degree w.length.", literature: true),
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
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
