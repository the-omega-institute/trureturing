using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GrahamObryantInverseSineRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GrahamObryantInverseSineRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/grahamobryant2005fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graham and O'Bryant's inverse-sine conditions admit noncanonical positive residue sets.",
        H("Graham-O'Bryant Conjecture 5.2: a signed-dyadic counterfamily"),
        Blocks(
            Paragraph(Text(
                "Fin(n) is the finite index type with natural values 0 through n-1. "
                + "All n and q are natural numbers; p maps Fin(n) to natural representatives. "
                + "real denotes the coercion to the real numbers, zmod(q,a) the natural cast "
                + "to ZMod(q), and val the least nonnegative representative. Inverse and "
                + "multiplication inside val are operations in ZMod(q), even for composite q. "
                + "The notation sumFin(i,n,f(i)) sums over every i in Fin(n); imageFin denotes "
                + "the ordinary finite image in the stated codomain. Fin(n) to N is a function "
                + "type, and injective(p) asserts pairwise distinct natural representatives.")),
            Node("complete-row", "The complete inverse-sine row", "row", RowFormula(),
                "The row includes i=k. For q>0 and any integers b(i) satisfying "
                + "p(i)b(i)=1 modulo q, it also equals the sum of "
                + "1/abs(sin(pi*real(p(k))*real(b(i))/real(q))). Integer representatives "
                + "differ by multiples of q; sine then changes by a sign, which disappears "
                + "under absolute value. Thus reducing the product before taking sine "
                + "preserves the author's modular-inverse convention.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("literal-conjecture", "The full source assertion", "claim", ClaimFormula(),
                "Conjecture 5.2, printed page 302, quantifies every positive n and q and "
                + "every list of n distinct positive representatives coprime to q. It assumes "
                + "the strict real inequality (7/4)^n<q, the natural sum bound sum p(i)<=q, "
                + "and the lower row bound for every k. The rational 7/4 is evaluated in R. "
                + "Both conclusions are required: q=2^n-1 and equality of the ordinary residue "
                + "set with all n powers 2^0,...,2^(n-1). No prime-modulus, field, omitted "
                + "diagonal, or independent-sign convention occurs in this assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("literal-refutation", "A noncanonical family and the refutation", "result",
                Disp(new Formula.Not(V("claim"))),
                "For every natural n>=3, set q=2^n-1 and p(i)=2^i except at i=n-1, "
                + "where p(i)=2^(n-1)-1. These n entries are positive, strictly below q, "
                + "distinct and coprime to q. Their finite image has cardinality n and their "
                + "sum is q-1. Induction from n=3 gives (7/4)^n<q. The last entry is "
                + "congruent to -2^(n-1); explicit signed powers give all modular inverses "
                + "without a primality assumption. Absolute sine removes those signs, "
                + "and i maps to k-i in Fin(n) permutes each complete row, including its "
                + "diagonal. With x=pi/q, all sin(2^j*x), 0<=j<n, are positive, while "
                + "sin(2^n*x)=-sin(x). The cotangent identity "
                + "1/sin(2t)=cot(t)-cot(2t) telescopes to zero over the shifted dyadic "
                + "orbit. Removing its final negative term and restoring its first term "
                + "gives every row exactly 2/sin(x). Every denominator is nonzero. "
                + "The last positive entry is neither 2^(n-1) nor any smaller power, so "
                + "the ordinary residue sets differ. This complete universal construction "
                + "precedes use of the conjecture. Specializing it to n=3 gives q=7 and "
                + "{1,2,3}, whose residue set differs from {1,2,4}; applying claim "
                + "would equate those sets. The resulting contradiction is Not claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("graham-obryant-inverse-sine-conjecture52-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula RowFormula()
    {
        var n = V("n");
        var q = V("q");
        var p = V("p");
        var k = V("k");
        var i = V("i");
        var product = Mul(Call("zmod", q, Apply(p, k)),
            Call("inv", Call("zmod", q, Apply(p, i))));
        var angle = Div(Mul(Pi, Real(Call("val", product))), Real(q));
        var term = Div(D(1), Call("abs", Call("sin", angle)));
        var body = Equal(Call("row", q, p, k), SumFinite("i", n, term));
        return Disp(All([("n", Naturals()), ("q", Naturals()),
            ("p", Functions(Fin(n), Naturals())), ("k", Fin(n))], body));
    }

    private static Formula ClaimFormula()
    {
        var n = V("n");
        var q = V("q");
        var p = V("p");
        var i = V("i");
        var k = V("k");
        var sourceSet = ImageFinite("i", n, Call("zmod", q, Apply(p, i)));
        var powers = ImageFinite("i", n, Pow(Call("zmod", q, D(2)), Call("val", i)));
        var quantified = All([("n", Naturals()), ("q", Naturals()),
            ("p", Functions(Fin(n), Naturals()))], Implies(
                Less(D(0), n), Less(D(0), q),
                Universal("i", Fin(n), Less(D(0), Apply(p, i))),
                Call("injective", p),
                Universal("i", Fin(n), Call("Coprime", Apply(p, i), q)),
                Less(Pow(Div(Real(D(7)), Real(D(4))), n), Real(q)),
                AtMost(SumFinite("i", n, Apply(p, i)), q),
                Universal("k", Fin(n), AtMost(
                    Div(Real(D(2)), Call("sin", Div(Pi, Real(q)))), Call("row", q, p, k))),
                And(Equal(q, Sub(Pow(D(2), n), D(1))), Equal(sourceSet, powers))));
        return Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, quantified));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Real(Formula value) => Call("real", value);
    private static Formula Functions(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula All((string Name, Formula Domain)[] variables, Formula body)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = Universal(variables[i].Name, variables[i].Domain, body);
        return body;
    }
    private static Formula SumFinite(string name, Formula n, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, Fin(n))), Sp, term);
    private static Formula ImageFinite(string name, Formula n, Formula term) =>
        Seq(OpenBrace, term, Sp, Mid, Sp, V(name), Sp, InMacro, Sp, Fin(n), CloseBrace);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.Implies, result);
        return result;
    }
}
