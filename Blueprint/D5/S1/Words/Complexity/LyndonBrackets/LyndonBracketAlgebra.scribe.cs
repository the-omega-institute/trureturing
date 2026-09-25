using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.LyndonBrackets;

internal sealed class LyndonBracketsLyndonBracketAlgebraDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive standard brackets are homogeneous integral word polynomials.",
        H("LyndonBracketAlgebra"),
        Blocks(
            Paragraph(Text(
                "The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, "
                + "standard factorization, and the triangular standard-bracket construction are "
                + "classical word and free-Lie-algebra material; the cited k-deck paper points to "
                + "Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean "
                + "implementation used by the later actual-positive-word construction.")),
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
                "For every word w, standardBracket w is homogeneous of degree w.length.", literature: true))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
