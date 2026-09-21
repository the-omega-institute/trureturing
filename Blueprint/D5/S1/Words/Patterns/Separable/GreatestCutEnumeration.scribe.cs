using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class GreatestCutEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/fu2019two");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(params Formula[] clauses) =>
        clauses.Aggregate(Both);
    private static Formula Total(Formula n) => Call("S", n);
    private static Formula Signed(Formula s, Formula n) => Call("P", s, n);
    private static Formula DeltaAt(Formula n) => Call("ite", Equal(n, D(1)), D(1), D(0));
    private static Formula Boundary(Formula s) => Call("ite", s, D(1), D(0));
    private static Formula Coeff(Formula p, Formula r) => Call("coeff", p, r);
    private static Formula Monomial(Formula p) => new Formula.Power(V("X"), Call("des", p));
    private static Formula SumOver(string v, Formula domain, Formula term) =>
        Seq(Sum, Underscore, Grp(V(v), InMacro, domain), term);
    private static Formula Splits(Formula n) => Call("PositiveSplit", n);
    private static Formula Rest(Formula n) => Subtract(n, V("m"));
    private static Formula Indicator(Formula n, Formula r) =>
        Call("ite", Both(Equal(n, D(1)), Equal(r, D(0))), D(1), D(0));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Greatest proper cuts give a literal weighted equivalence and exact finite descent recurrences.",
        H("Greatest cuts and finite descent enumeration"),
        Blocks(
            Paragraph(Text(
                "Theorem 2.3 of Fu, Lin and Zeng uses the greatest valid cut of an actual "
                + "2413/3142-avoiding permutation. Its right factor is a singleton or has the "
                + "opposite sign. The finite signed identities below are the actual-permutation "
                + "form of equations (2.4) and (2.5) in the proof of Corollary 2.4. "
                + "False denotes direct sum and true denotes skew sum. Avoider(n), Cut, "
                + "blockSum and des denote the literal objects and ordinary adjacent descents "
                + "from the fixed-cut construction. Subtype elements are evaluated through their "
                + "underlying permutations. Every polynomial has natural coefficients. "
                + "These classical enumeration statements do not resolve the real-rootedness "
                + "assertion of Conjecture 5.2.")),
            Node("HasProperCut", "Proper oriented cuts", DescribeRole.Definition,
                All("n", N, All("s", V("Bool"), All("p", Call("Perm", V("n")),
                    new Formula.Logic(Call("HasProperCut", V("s"), V("p")), FormulaLogicOperator.Iff,
                        Some("m", N, Conjunction(Less(D(0), V("m")), Less(V("m"), V("n")),
                            Call("Cut", V("s"), V("p"), V("m")))))))),
                "The cut position is strictly between zero and the length. Both factors are nonempty."),
            Node("PositiveSplit", "Positive position splits", DescribeRole.Definition,
                All("n", N, Equal(Splits(V("n")),
                    Seq(OpenBrace, V("m"), InMacro, Call("Fin", V("n")), Mid, Sp,
                        D(0), Lt, V("m"), CloseBrace))),
                "A split is a natural position m with 0<m<n. Its right length is n-m. "
                + "In the formulas a split is identified with its natural value; this identification "
                + "does not add or duplicate any objects."),
            Node("SignedAvoider", "The two proper signed classes", DescribeRole.Definition,
                All("s", V("Bool"), All("n", N,
                    Equal(Call("SignedAvoider", V("s"), V("n")),
                        Seq(OpenBrace, V("p"), InMacro, Call("Avoider", V("n")), Mid, Sp,
                            Call("HasProperCut", V("s"), V("p")), CloseBrace)))),
                "Membership carries a proof of a proper cut, rather than a chosen cut. "
                + "Proof fields do not multiply the number of permutations."),
            Node("RightFactor", "The permitted right factors", DescribeRole.Definition,
                All("s", V("Bool"), All("k", N,
                    Equal(Call("RightFactor", V("s"), V("k")),
                        Seq(OpenBrace, V("b"), InMacro, Call("Avoider", V("k")), Mid, Sp,
                            Or(Equal(V("k"), D(1)),
                                Call("HasProperCut", Call("not", V("s")), V("b"))), CloseBrace)))),
                "The left factor is unrestricted within the actual avoidance class. The right "
                + "factor is a singleton or is properly decomposable in the opposite orientation. "
                + "Neither orientation reverses positions or values inside either factor."),
            Node("Factors", "Dependent pairs of actual factors", DescribeRole.Definition,
                All("s", V("Bool"), All("n", N,
                    Equal(Call("Factors", V("s"), V("n")),
                        Seq(Sigma, Underscore, Grp(V("m"), InMacro, Splits(V("n"))),
                            Call("Avoider", V("m")), Times,
                            Call("RightFactor", V("s"), Rest(V("n"))))))),
                "An element is a triple (m,a,b), with a of length m and b of length n-m. "
                + "The dependent index fixes the factor lengths before their values are compared."),
            Node("S", "The ordinary descent polynomial", DescribeRole.Definition,
                All("n", N, Equal(Total(V("n")), Call("ite", Equal(V("n"), D(0)), D(0),
                    SumOver("p", Call("Avoider", V("n")), Monomial(V("p")))))),
                "The unique empty permutation is still an actual avoider. The definition of S "
                + "assigns length zero the polynomial zero; it does not change that avoidance class."),
            Node("P", "Unpadded signed descent polynomials", DescribeRole.Definition,
                All("s", V("Bool"), All("n", N, Equal(Signed(V("s"), V("n")),
                    SumOver("p", Call("SignedAvoider", V("s"), V("n")), Monomial(V("p")))))),
                "P(false,n) and P(true,n) count the proper direct and skew classes. Both vanish "
                + "at lengths zero and one. The source pads each signed sequence by one at "
                + "length one; its padded sequences are delta(n)+P(false,n) and delta(n)+P(true,n), "
                + "where delta(n)=ite(n=1,1,0). The source's derangement polynomial is a "
                + "different object."),
            Paragraph(Text(
                "For x=(m,a,b), write m(x), a(x), b(x) for its three projections. In the next "
                + "formula cast(n,q) transports a permutation of length m+(n-m) to length n "
                + "along that natural-number equality alone. Equiv(A,B) is the type of mutually "
                + "inverse maps between A and B. The notation not(s) is Boolean negation. "
                + "Each finite sum over PositiveSplit(n) uses k=n-m; antidiagonal(r) consists "
                + "of ordered pairs (a,b) of natural numbers satisfying a+b=r. "
                + "All clauses of the following statement hold together.")),
            Node("result", "The weighted equivalence and exact recurrences", DescribeRole.Theorem,
                Conjunction(EquivalenceStatement(), InitialStatement(), TotalStatement(),
                    RecurrenceStatement(), TotalCoefficients(), SignedCoefficients(false),
                    All("n", N, Equal(Coeff(Signed(V("true"), V("n")), D(0)), D(0))),
                    SignedCoefficients(true)),
                "At the first and last positions, opposite proper cuts would give contradictory "
                + "strict inequalities. A cut at m+r in blockSum(s,a,b) is exactly a cut at r "
                + "in b, including r=0. Consequently a greatest proper cut leaves no same-sign "
                + "proper cut in its right factor. Proper-cut existence then gives precisely the "
                + "singleton-or-opposite condition. Conversely that condition excludes every "
                + "larger cut of the assembled permutation. Equality of two assemblies forces "
                + "equality of their greatest split positions; only after identifying these "
                + "dependent indices does fixed-cut uniqueness identify the factors. "
                + "The descent law gives the weight and the resulting literal equivalence "
                + "reindexes the finite sums. The coefficient identities follow from polynomial "
                + "multiplication and the shift by X. In particular the skew constant coefficient "
                + "is zero; its remaining coefficients use r+1, without truncated subtraction."),
            Paragraph(Text(
                "The finite factor equivalence is not a formal construction of the full di-sk-tree "
                + "bijection. Generating-function equations, gamma identities, and the analytic "
                + "real-rootedness argument are separate statements.")))));

    private static Formula EquivalenceStatement()
    {
        var n = V("n");
        var s = V("s");
        var x = V("x");
        var m = Call("m", x);
        var a = Call("a", x);
        var b = Call("b", x);
        var p = Call("e", x);
        return All("s", V("Bool"), All("n", N,
            Some("e", Call("Equiv", Call("Factors", s, n), Call("SignedAvoider", s, n)),
                All("x", Call("Factors", s, n), Conjunction(
                    Equal(p, Call("cast", n, Call("blockSum", s, a, b))),
                    Call("Cut", s, p, m),
                    All("r", N, Imp(Conjunction(Less(D(0), V("r")), Less(V("r"), n),
                        Call("Cut", s, p, V("r"))), AtMost(V("r"), m))),
                    Equal(Call("des", p),
                        Add(Add(Call("des", a), Call("des", b)), Boundary(s))))))));
    }

    private static Formula InitialStatement() => Conjunction(
        Equal(Total(D(0)), D(0)), Equal(Total(D(1)), D(1)),
        All("s", V("Bool"), Both(Equal(Signed(V("s"), D(0)), D(0)),
            Equal(Signed(V("s"), D(1)), D(0)))));

    private static Formula TotalStatement() => All("n", N,
        Equal(Total(V("n")), Add(Add(DeltaAt(V("n")), Signed(V("false"), V("n"))),
            Signed(V("true"), V("n")))));

    private static Formula RecurrenceStatement() => All("s", V("Bool"), All("n", N,
        Equal(Signed(V("s"), V("n")), Multiply(new Formula.Power(V("X"), Boundary(V("s"))),
            SumOver("m", Splits(V("n")), Multiply(Total(V("m")),
                Add(DeltaAt(Rest(V("n"))), Signed(Call("not", V("s")), Rest(V("n"))))))))));

    private static Formula TotalCoefficients() => All("n", N, All("r", N,
        Equal(Coeff(Total(V("n")), V("r")),
            Add(Add(Indicator(V("n"), V("r")), Coeff(Signed(V("false"), V("n")), V("r"))),
                Coeff(Signed(V("true"), V("n")), V("r"))))));

    private static Formula SignedCoefficients(bool skew)
    {
        var n = V("n");
        var r = V("r");
        var ab = V("ab");
        var a = Call("fst", ab);
        var b = Call("snd", ab);
        return All("n", N, All("r", N,
            Equal(Coeff(Signed(V(skew ? "true" : "false"), n), skew ? Add(r, D(1)) : r),
                SumOver("m", Splits(n), SumOver("ab", Call("antidiagonal", r),
                    Multiply(Coeff(Total(V("m")), a),
                        Add(Indicator(Rest(n), b),
                            Coeff(Signed(V(skew ? "false" : "true"), Rest(n)), b))))))));
    }

    private static DocumentBlock Node(
        string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}
