using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GaussianQuotient;

internal sealed class MirzavaziriYaqubiMonotonicityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mirzavaziri2026gaussianquotient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak increase of a Gaussian quotient permits an extra negative coefficient.",
        H("A negative answer to the final question of Problem 7.2"),
        Blocks(
            Node("increasing-from-one", "Weak increase from coefficient one", "increasingFromOne",
                All("U", Polynomials(), Iff(Call("increasingFromOne", F.Id("U")),
                    IncreasingBody(F.Id("U")))),
                "The source asks whether the first quotient is “weakly increasing from "
                    + "q¹ to its middle coefficient” (Problem 7.2, p. 16). "
                    + "The comparisons begin with the coefficients of degrees one and two "
                    + "and end at the natural-number quotient of natDegree U by two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                SourceQuestion()),
            Node("two-exceptions", "The proposed coefficient signs", "twoExceptionSignPattern",
                All("P", Polynomials(), Iff(Call("twoExceptionSignPattern", F.Id("P")),
                    SignBody(F.Id("P")))),
                "The source requests a polynomial “whose only negative coefficients are "
                    + "−1 at q¹ and at qᴰ⁻¹” (Problem 7.2, p. 16). "
                    + "Here D is natDegree P. Every other natural index, including the "
                    + "zero coefficients past the degree, is required to be nonnegative.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("universal-question", "The final universal sufficiency question", "claim",
                Iff(Call("claim"), ClaimBody()),
                "N, k, a and b are natural numbers with k ≤ N and "
                    + "a,b ≥ 1; U and P are integer polynomials. The two multiplication "
                    + "equalities express exact polynomial quotients. gauss is the "
                    + "existing q-Pascal Gaussian polynomial, and qInteger is the "
                    + "finite geometric sum, mapped from natural to integer coefficients. "
                    + "The question concerns weak increase through the middle of U; "
                    + "the exceptional degree D−1 is calculated from P. "
                    + "Nat.div(m,2) is natural-number division, equal to floor(m/2). "
                    + "All index subtraction is natural subtraction, truncated at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                SourceQuestion()),
            Node("negative-answer", "The universal assertion is false", "result",
                new Formula.Not(Parenthesized(ClaimBody())),
                "At (N,k,a,b)=(30,3,7,10), exact quotients U and P have degrees 75 "
                    + "and 66. U increases weakly from coefficient one through "
                    + "coefficient 37, but the coefficient of degree 11 in P is −1. "
                    + "That index differs from both 1 and 65. The Gaussian hook and "
                    + "symmetry identities establish the first quotient, and explicit "
                    + "polynomial arithmetic establishes the second. This answers the "
                    + "final sufficiency question; the classification of all quadruples "
                    + "and an unbounded family are not asserted by this theorem.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        DocumentBlock? quotation = null, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            quotation is null ? Blocks(Paragraph(Text(prose)))
                : Blocks(quotation, Paragraph(Text(prose))), role, resolution);

    private static DocumentBlock SourceQuestion()
    {
        var q = F.Id("q");
        var gaussian = new Formula.Subscript(Seq(Begin, Grp(F.Id("bmatrix")),
            F.Id("N"), RowBreak, F.Id("k"), End, Grp(F.Id("bmatrix"))), q);
        var qa = new Formula.Subscript(Seq(OpenBracket, F.Id("a"), CloseBracket), q);
        var qb = new Formula.Subscript(Seq(OpenBracket, F.Id("b"), CloseBracket), q);
        return Paragraph(Text("Problem 7.2, p. 16: “Characterize the quadruples "),
            Math(Parenthesized(Seq(F.Id("N"), Comma, F.Id("k"), Comma,
                F.Id("a"), Comma, F.Id("b")))),
            Text(" for which "), Math(Seq(gaussian, Slash, Parenthesized(Seq(qa, qb)))),
            Text(" is a polynomial whose only negative coefficients are "),
            Math(MinusOne()), Text(" at "), Math(new Formula.Power(q, D(1))),
            Text(" and at "), Math(new Formula.Power(q, Sub(F.Id("D"), D(1)))),
            Text(". In particular, is this always the case when "),
            Math(Seq(gaussian, Slash, qa)), Text(" is weakly increasing from "),
            Math(new Formula.Power(q, D(1))), Text(" to its middle coefficient?”"));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Apply(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Polynomials() => Call("Polynomial", Ints());
    private static Formula Coeff(Formula p, Formula t) => Qualified("Polynomial", "coeff", p, t);
    private static Formula Degree(Formula p) => Qualified("Polynomial", "natDegree", p);
    private static Formula MinusOne() => Seq(Minus, D(1));

    private static Formula IncreasingBody(Formula u)
    {
        var s = F.Id("s");
        return All("s", Nat(), Imp(Le(D(2), s),
            Imp(Le(s, Qualified("Nat", "div", Degree(u), D(2))),
                Le(Coeff(u, Sub(s, D(1))), Coeff(u, s)))));
    }

    private static Formula SignBody(Formula p)
    {
        var t = F.Id("t");
        var penultimate = Sub(Degree(p), D(1));
        return And(Eq(Coeff(p, D(1)), MinusOne()),
            And(Eq(Coeff(p, penultimate), MinusOne()),
                All("t", Nat(), Imp(Ne(t, D(1)),
                    Imp(Ne(t, penultimate), Le(D(0), Coeff(p, t)))))));
    }

    private static Formula MappedInteger(Formula a) =>
        Qualified("Polynomial", "map", Qualified("Nat", "castRingHom", Ints()),
            Call("qInteger", a));

    private static Formula ClaimBody()
    {
        var n = F.Id("N");
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var u = F.Id("U");
        var p = F.Id("P");
        return All("N", Nat(), All("k", Nat(), All("a", Nat(), All("b", Nat(),
            Imp(Le(k, n), Imp(Le(D(1), a), Imp(Le(D(1), b),
                All("U", Polynomials(), All("P", Polynomials(),
                    Imp(Eq(Call("gauss", n, k), Mul(MappedInteger(a), u)),
                        Imp(Eq(u, Mul(MappedInteger(b), p)),
                            Imp(Call("increasingFromOne", u),
                                Call("twoExceptionSignPattern", p)))))))))))));
    }
}
