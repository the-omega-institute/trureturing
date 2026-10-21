using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class ShalaCosetLikeAtomisticLatticeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/shala2024cosetlike");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite lattice separates weak and strong coset-likeness.",
        H("A twelve-element atomistic lattice answers Question 7.4"),
        Blocks(
            Node("join-irreducibles", "The join-irreducible set", "J", JFormula(),
                "For a finite bounded lattice L, J is the finite set of elements satisfying Mathlib's SupIrred predicate.", AssessedProvenance.FromLiterature(Source)),
            Node("join-irreducibles-below", "Join-irreducibles below an element", "Jx", JxFormula(),
                "Jx x filters J by the order relation j ≤ x.", AssessedProvenance.FromLiterature(Source)),
            Node("index", "The atom-index ratio", "index", IndexFormula(),
                "index x is the rational ratio of the cardinality of J to the cardinality of Jx x.", AssessedProvenance.FromLiterature(Source)),
            Node("probabilistic-zeta", "The probabilistic zeta function", "P", PFormula(),
                "P L s sums the upper-interval Möbius coefficients over all elements except bottom, weighted by the complex power of the rational index.", AssessedProvenance.FromLiterature(Source)),
            Node("strongly-coset-like", "Strong coset-likeness", "StronglyCosetLike", StrongFormula(),
                "Strong coset-likeness requires the cardinality of Jx x to divide the cardinality of J for every non-bottom element.", AssessedProvenance.FromLiterature(Source)),
            Node("weakly-coset-like", "Weak coset-likeness", "WeaklyCosetLike", WeakFormula(),
                "Weak coset-likeness requires P L s to have a finite ordinary Dirichlet-series representation with integer coefficients.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal form of Question 7.4", "claim", ClaimFormula(),
                "Question 7.4 asks verbatim: ‘Does there exist a weakly coset-like atomistic lattice that is not strongly coset-like?’ The formal claim is its universal negation: every finite atomistic weakly coset-like lattice is strongly coset-like.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The universal implication is false"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The twelve-element lattice has eight singleton join-irreducibles. Its element x has three join-irreducibles below it, so 3 does not divide 8. The upper Möbius coefficient of x vanishes, and the remaining terms give P L s = 1 − 2^(−s) − 4·8^(−s), an ordinary Dirichlet series. Thus the lattice is weakly coset-like but not strongly coset-like, refuting the universal implication and answering the question affirmatively. The d-divisible partition-lattice question and minimality are not settled here."))),
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rational() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Lattice(Formula l) => Seq(OpenBracket, Call("Lattice", l), CloseBracket);
    private static Formula BoundedOrder(Formula l) => Seq(OpenBracket, Call("BoundedOrder", l), CloseBracket);
    private static Formula Fintype(Formula l) => Seq(OpenBracket, Call("Fintype", l), CloseBracket);
    private static Formula DecidableEq(Formula l) => Seq(OpenBracket, Call("DecidableEq", l), CloseBracket);
    private static Formula DecidableLE(Formula l) => Seq(OpenBracket, Call("DecidableLE", l), CloseBracket);
    private static Formula LocallyFiniteOrder(Formula l) => Seq(OpenBracket, Call("LocallyFiniteOrder", l), CloseBracket);
    private static Formula Finset(Formula l) => Call("Finset", l);
    private static Formula Scope(Formula l, Formula body, bool withEq = false, bool withLE = false, bool withLocal = false) {
        var parts = new List<Formula> { Lattice(l), Sp, BoundedOrder(l), Sp, Fintype(l) };
        if (withEq) parts.AddRange(new[] { Sp, DecidableEq(l) });
        if (withLE) parts.AddRange(new[] { Sp, DecidableLE(l) });
        if (withLocal) parts.AddRange(new[] { Sp, LocallyFiniteOrder(l) });
        parts.AddRange(new[] { Comma, Esc, body });
        return Seq(parts.ToArray());
    }
    private static Formula JFormula() {
        var l = F.Id("L");
        var univ = Cast(Qualified("Finset", "univ"), Finset(l));
        var filtered = At(Qualified("Finset", "filter"), F.Id("SupIrred"), univ);
        return All("L", Type(), Scope(l, Equal(Call("J", l), filtered)));
    }
    private static Formula JxFormula() {
        var l = F.Id("L"); var x = F.Id("x"); var j = F.Id("j");
        var filtered = At(Qualified("Finset", "filter"), LambdaOf("j", l, LessEqual(j, x)), Call("J", l));
        return All("L", Type(), Scope(l,
            All("x", l, Equal(Call("Jx", x), filtered)), withEq: false, withLE: true));
    }
    private static Formula IndexFormula() {
        var l = F.Id("L"); var x = F.Id("x");
        var rhs = Divide(Cast(At(Qualified("Finset", "card"), Call("J", l)), Rational()), Cast(At(Qualified("Finset", "card"), Call("Jx", x)), Rational()));
        return All("L", Type(), Scope(l, All("x", l, Equal(Call("index", x), rhs)), withEq: false, withLE: true));
    }
    private static Formula PFormula() {
        var l = F.Id("L"); var s = F.Id("s"); var x = F.Id("x");
        var univ = Cast(Qualified("Finset", "univ"), Finset(l));
        var erase = At(Qualified("Finset", "erase"), univ, Cast(Qualified("Bot", "bot"), l));
        var mu = At(Qualified("IncidenceAlgebra", "mu"), Int(), x, Cast(Qualified("Top", "top"), l));
        var term = Times(Cast(mu, Complex()), Pow(Cast(Cast(Call("index", x), Rational()), Complex()), Neg(s)));
        var sum = At(Qualified("Finset", "sum"), erase, LambdaOf("x", l, term));
        return All("L", Type(), Scope(l,
            All("s", Complex(), Equal(Call("P", s), sum)), withEq: true, withLE: true, withLocal: true));
    }
    private static Formula StrongFormula() {
        var l = F.Id("L"); var x = F.Id("x");
        var premise = NotEqual(x, Cast(Qualified("Bot", "bot"), l));
        var divisibility = Divides(At(Qualified("Finset", "card"), Call("Jx", x)), At(Qualified("Finset", "card"), Call("J", l)));
        var body = All("x", l, Implies(premise, divisibility));
        return All("L", Type(), Scope(l, Equal(Call("StronglyCosetLike", l), Parenthesized(body)), withEq: false, withLE: true));
    }
    private static Formula WeakFormula() {
        var l = F.Id("L"); var n = F.Id("n"); var a = F.Id("a"); var s = F.Id("s");
        var coeff = Times(Cast(Call("a", n), Complex()), Pow(Cast(n, Complex()), Neg(s)));
        var sum = At(Qualified("Finset", "sum"),
            At(Qualified("Finset", "Icc"), D(1), F.Id("N")), LambdaOf("n", Nat(), coeff));
        var rep = Exists("N", Nat(), Exists("a", new Formula.TypeArrow(Nat(), Int()),
            All("s", Complex(), Equal(Call("P", s), sum))));
        return All("L", Type(), Scope(l,
            Equal(Call("WeaklyCosetLike", l), Parenthesized(rep)), withEq: true, withLE: true, withLocal: true));
    }
    private static Formula ClaimBody() {
        var l = F.Id("L");
        return All("L", Type(), Seq(
            OpenBracket, Call("Lattice", l), CloseBracket, Sp,
            OpenBracket, Call("BoundedOrder", l), CloseBracket, Sp,
            OpenBracket, Call("Fintype", l), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", l), CloseBracket, Sp,
            OpenBracket, Call("DecidableLE", l), CloseBracket, Sp,
            OpenBracket, Call("LocallyFiniteOrder", l), CloseBracket, Sp,
            Implies(Call("IsAtomistic", l), Implies(Call("WeaklyCosetLike", l), Call("StronglyCosetLike", l)))));
    }
    private static Formula ClaimFormula() => ClaimBody();
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Cast(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divides(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Times(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Neg(Formula a) => Seq(Minus, Sp, Parenthesized(a));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
