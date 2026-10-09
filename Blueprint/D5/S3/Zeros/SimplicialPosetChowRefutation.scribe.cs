using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class SimplicialPosetChowRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/SimplicialPosetChowRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/hosterstump2025chow");
    private const string Conjecture =
        "Let P be a simplicial poset. Then H_P̂(x), H_P̂*(x) and H^aug_P̂(x) are real-rooted. "
        + "Moreover, the roots of both H_P̂(x) and H_P̂*(x) interlace the roots of "
        + "H^aug_P̂(x) = H^aug_P̂*(x).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two tetrahedra sharing a vertex have a non-real-rooted Chow polynomial.",
        H("A simplicial-poset Chow counterexample"),
        Blocks(
            Node("rank", "Rank in the original poset", RankFormula(),
                "Section 1, p. 1 uses the rank of a face. The rank is (Order.height x).toNat: "
                + "the number of strict steps from the bottom to x in a finite graded poset."),
            Node("simplicial", "Finite graded simplicial posets", SimplicialFormula(),
                "Section 1, p. 1: “Let P be a finite graded simplicial poset. This is, P is a "
                + "finite poset with 0̂ for which all maximal intervals are boolean of the same rank n.” "
                + "Set.Iic m is the lower interval. The subset order on Finset (Fin n) is the "
                + "Boolean lattice of rank n. The assumptions include Fintype, DecidableEq, "
                + "PartialOrder and OrderBot; no positivity assumption on the h-vector is added."),
            Node("alpha", "The flag f-vector", AlphaFormula(),
                "Section 1, p. 1: “for α_P̂(T) being the flag f-vector counting maximal chains "
                + "in the subposet of P̂ with only the ranks in T selected.” "
                + "The selected subtype Q of WithTop P contains bottom, the added top, and "
                + "elements of intrinsic rank in T. WithTop.recTopCoe gives the added top "
                + "rank n+1 and original elements rank (Order.height x).toNat. The powerset "
                + "filter counts exactly IsMaxChain sets. Example 1.3 fixes α(∅)=1. "
                + "A consumed private lemma equates this literal count and the computation "
                + "on P₂ for the isolated rank sets in {2,…,4}, which include all "
                + "subsets required by the β sums in (1.1)."),
            Node("beta", "The flag h-vector", BetaFormula(),
                "Section 1, p. 1 defines β_P̂(S) = Σ_{T⊆S} (−1)^{|S∖T|} α_P̂(T). "
                + "The sum is over S.powerset, with integer coefficients and the natural "
                + "count alpha P n T explicitly cast to integers."),
            Node("isolated", "Isolated rank sets", IsolatedFormula(),
                "Section 1, p. 1: “Here, a set S ⊂ ℤ is isolated if i ∈ S implies i+1 ∉ S.” "
                + "The selected ranks are natural numbers; the same adjacency condition applies."),
            Node("H", "The Chow polynomial", HFormula(),
                "Section 1, p. 1, (1.1): H_P̂(x) = Σ_{S⊆{2,…,n}, S isolated} "
                + "β_P̂(S) x^{|S|} (1+x)^{n−2|S|}. The formal polynomial has integer coefficients. "
                + "The filter selects isolated subsets of Finset.Icc 2 n. The exponent uses "
                + "natural-number subtraction; C is Polynomial.C and X is Polynomial.X."),
            Node("claim", "The first real-rootedness assertion", ClaimFormula(),
                "Conjecture 1.5, p. 3: “" + Conjecture + "” "
                + "The claim quantifies over every finite partial order P with bottom and every "
                + "n : ℕ, and asserts simplicial P n → "
                + "D5.S3.Zeros.Jensen.JensenPolynomialObstruction.PolynomialHyperbolic "
                + "((H P n).map (Int.castRingHom ℝ)). The predicate says every "
                + "complex zero of the real coefficient polynomial is real. It is the first "
                + "real-rootedness assertion, which the full conjecture implies."),
            Node("result", "Conjecture 1.5 is false", Seq(Neg, Sp, Op("claim")),
                "The face poset consists of all subsets of {0,1,2,3} or {0,4,5,6}, ordered "
                + "by inclusion, with the empty face as bottom. Each maximal interval is "
                + "Boolean of rank four. Its flag f-values on ∅, {2}, {3}, {4}, {2,4} are "
                + "1, 12, 8, 2, 12, giving flag h-values 1, 11, 7, 1, −1. Thus (1.1) is "
                + "X⁴+23X³+43X²+23X+1. Put a=(23−√365)/2 and b=(23+√365)/2. "
                + "The polynomial factors as (X²+aX+1)(X²+bX+1). Since 0<a<2, "
                + "z=(−a+i√(4−a²))/2 is a zero with positive imaginary part. "
                + "This contradicts the universal first assertion.", true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool theorem = false) => Describe.Lean(
            DescribeId.Create("simplicial-chow-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(DefinitionDsl.Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hoster-stump-2025-chow-polynomials-simplicial-posets"),
                ResolutionKind.Refuted) : null);

    private static Formula Id(string value) => F.Id(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Qualified(string owner, string member) => Seq(Op(owner), Dot, Op(member));
    private static Formula Apply(Formula function, params Formula[] args)
    {
        var items = new List<Formula>();
        foreach (var arg in args) { if (items.Count > 0) items.Add(Comma); items.Add(arg); }
        return Seq(function, Parenthesized(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Inst(string name) => Seq(OpenBracket, Call(name, Id("P")), CloseBracket);
    private static Formula PosetBinders(bool finite = true, bool decidableOrder = false, bool bottom = false)
    {
        var items = new List<Formula> { Forall, Sp, Parenthesized(Seq(Id("P"), Colon, Op("Type"))) };
        if (finite) { items.Add(Inst("Fintype")); items.Add(Inst("DecidableEq")); }
        items.Add(Inst("PartialOrder"));
        if (decidableOrder) items.Add(Inst("DecidableLE"));
        if (bottom) items.Add(Inst("OrderBot"));
        return Seq([.. items]);
    }
    private static Formula Var(string name, Formula type) => Parenthesized(Seq(Id(name), Colon, type));
    private static Formula Nat => Op("Nat");
    private static Formula Integer => new Formula.Integers();
    private static Formula FinsetNat => Call("Finset", Nat);
    private static Formula Card(Formula x) => Seq(Parenthesized(x), Dot, Op("card"));
    private static Formula Powerset(Formula x) => Seq(Parenthesized(x), Dot, Op("powerset"));
    private static Formula Eqn(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Arrow(Formula lhs, Formula rhs) => new Formula.Logic(lhs, FormulaLogicOperator.Implies, rhs);
    private static Formula Typed(Formula x, Formula type) => Parenthesized(Seq(x, Colon, type));
    private static Formula RankFormula() => Seq(PosetBinders(false), Var("x", Id("P")), Comma,
        Eqn(Call("rank", Id("x")), Seq(Parenthesized(Apply(Qualified("Order", "height"), Id("x"))), Dot, Op("toNat"))));
    private static Formula SimplicialFormula() => Seq(PosetBinders(bottom: true), Var("n", Nat), Comma,
        Eqn(Call("simplicial", Id("P"), Id("n")), Parenthesized(Seq(Forall, Sp, Var("m", Id("P")), Comma,
            Arrow(Call("IsMax", Id("m")), Call("Nonempty", Call("OrderIso",
                Apply(Qualified("Set", "Iic"), Id("m")),
                Call("Finset", Call("Fin", Id("n"))))))))));
    private static Formula AlphaFormula()
    {
        var x = Id("x");
        var rank = Apply(Qualified("WithTop", "recTopCoe"), Seq(Id("n"), Plus, D(1)),
            Typed(Op("rank"), new Formula.TypeArrow(Id("P"), Nat)), x);
        var selected = Seq(OpenBrace, x, Colon, Call("WithTop", Id("P")), Sp, Mid, Sp,
            new Formula.Logic(Eqn(x, Qualified("Bot", "bot")), FormulaLogicOperator.Or,
                new Formula.Logic(Eqn(x, Qualified("Top", "top")), FormulaLogicOperator.Or,
                    new Formula.Relation(rank, FormulaRelationOperator.MemberOf, Id("T")))), CloseBrace);
        var q = Id("Q"); var c = Id("C");
        var chains = Apply(Seq(Parenthesized(Powerset(Typed(Qualified("Finset", "univ"),
                Call("Finset", q)))), Dot, Op("filter")),
            Seq(LambdaLower, Sp, Var("C", Call("Finset", q)), Comma,
                Call("IsMaxChain", Parenthesized(Seq(Cdot, Sp, Le, Sp, Cdot)),
                    Typed(c, Call("Set", q)))));
        return Seq(PosetBinders(bottom: true), Var("n", Nat), Var("T", FinsetNat), Comma,
            Eqn(Call("alpha", Id("P"), Id("n"), Id("T")),
                Seq(Op("let"), Sp, q, Colon, Op("Type"), Eq, selected, Semi, Card(chains))));
    }
    private static Formula BetaFormula() => Seq(PosetBinders(bottom: true),
        Var("n", Nat), Var("S", FinsetNat), Comma,
        Eqn(Call("beta", Id("P"), Id("n"), Id("S")),
            Seq(new Formula.Subscript(Sum,
                new Formula.Relation(Id("T"), FormulaRelationOperator.MemberOf, Powerset(Id("S")))),
                new Formula.Power(Parenthesized(Seq(Minus, D(1))),
                    Card(Seq(Id("S"), Setminus, Sp, Id("T")))), Cdot, Sp,
                Typed(Call("alpha", Id("P"), Id("n"), Id("T")), Integer))));
    private static Formula IsolatedFormula() => Seq(Forall, Sp, Var("S", FinsetNat), Comma,
        Eqn(Call("isolated", Id("S")), Parenthesized(Seq(Forall, Sp, Id("i"), InMacro, Sp, Id("S"), Comma,
            Neg, Sp, Parenthesized(Seq(Id("i"), Plus, D(1), InMacro, Sp, Id("S")))))));
    private static Formula HFormula()
    {
        var s = Id("S");
        var selected = Apply(Seq(Parenthesized(Powerset(Apply(Qualified("Finset", "Icc"), D(2), Id("n")))),
            Dot, Op("filter")), Op("isolated"));
        return Seq(PosetBinders(bottom: true), Var("n", Nat), Comma,
            Eqn(Call("H", Id("P"), Id("n")),
                Seq(new Formula.Subscript(Sum,
                    new Formula.Relation(s, FormulaRelationOperator.MemberOf, selected)),
                    Apply(Qualified("Polynomial", "C"), Call("beta", Id("P"), Id("n"), s)), Cdot, Sp,
                    new Formula.Power(Qualified("Polynomial", "X"), Card(s)), Cdot, Sp,
                    new Formula.Power(Parenthesized(Seq(D(1), Plus, Qualified("Polynomial", "X"))),
                        Seq(Id("n"), Minus, D(2), Cdot, Sp, Card(s))))));
    }
    private static Formula ClaimFormula() => Eqn(Op("claim"), Parenthesized(Seq(PosetBinders(bottom: true),
        Var("n", Nat), Comma, Arrow(Call("simplicial", Id("P"), Id("n")),
            Apply(Seq(Op("D5"), Dot, Op("S3"), Dot, Op("Zeros"), Dot, Op("Jensen"), Dot,
                    Op("JensenPolynomialObstruction"), Dot, Op("PolynomialHyperbolic")),
                Apply(Seq(Parenthesized(Call("H", Id("P"), Id("n"))), Dot, Op("map")),
                    Apply(Qualified("Int", "castRingHom"), Op("Real"))))))));
}
