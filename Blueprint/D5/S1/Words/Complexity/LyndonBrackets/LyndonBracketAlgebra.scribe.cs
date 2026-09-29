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
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "WordPolynomial" => Equal(Call("WordPolynomial", F.Id("A")),
            Call("MonoidAlgebra", F.Id("Z"), Call("FreeMonoid", F.Id("A")))),
        "wordMonomial" => Seq(Forall, Sp, F.Id("w"), Comma,
            Equal(Call("wordMonomial", F.Id("w")),
                Call("single", Call("ofList", F.Id("w")), Num(1)))),
        "Homogeneous" => Seq(Forall, Sp, F.Id("p"), Comma, F.Id("n"),
            Comma, Call("Homogeneous", F.Id("p"), F.Id("n")), Iff,
            Forall, Sp, F.Id("m"), InMacro, Call("support", F.Id("p")),
            Comma, Equal(Call("length", F.Id("m")), F.Id("n"))),
        "HasLeadingWord" => Seq(Forall, Sp, F.Id("p"), Comma, F.Id("w"),
            Comma, Call("HasLeadingWord", F.Id("p"), F.Id("w")), Iff,
            Call("Homogeneous", F.Id("p"), Call("length", F.Id("w"))), Land,
            Equal(Call("coeff", F.Id("p"), Call("ofList", F.Id("w"))), Num(1)),
            Land, Forall, Sp, F.Id("m"), InMacro, Call("support", F.Id("p")),
            Comma, F.Id("w"), Leq, Call("toList", F.Id("m"))),
        "commutator" => Seq(Forall, Sp, F.Id("p"), Comma, F.Id("q"),
            Comma, Equal(Call("commutator", F.Id("p"), F.Id("q")),
                Subtract(Multiply(F.Id("p"), F.Id("q")),
                    Multiply(F.Id("q"), F.Id("p"))))),
        "standardBracket" => Seq(
            Equal(Call("standardBracket", F.Id("empty")), Num(0)), Land,
            Open, Forall, Sp, F.Id("a"), Comma,
            Equal(Call("standardBracket", Call("singleton", F.Id("a"))),
                Call("wordMonomial", Call("singleton", F.Id("a")))), Close, Land,
            Forall, Sp, F.Id("w"), Comma,
            F.D(2), Leq, Call("length", F.Id("w")), Rightarrow,
            Equal(Call("standardBracket", F.Id("w")),
                Call("commutator", Call("standardBracket",
                        Call("standardLeft", F.Id("w"))),
                    Call("standardBracket", Call("standardRight", F.Id("w")))))),
        "standardBracket_homogeneous" => Seq(Forall, Sp, F.Id("w"),
            Comma, Call("Homogeneous", Call("standardBracket", F.Id("w")),
                Call("length", F.Id("w")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
