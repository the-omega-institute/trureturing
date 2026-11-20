using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DyadicExtendedStirlingBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kurkov2024a358612");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal rational extended Stirling array satisfies Kurkov's complete dyadic block identity.",
        H("Dyadic blocks of the extended Stirling array"),
        Blocks(
            Paragraph(Text(
                "Mikhail Kurkov's OEIS A358612 defines extended Stirling numbers through the binary expansion of the row index. "
                + "All row and column indices below are natural numbers, including zero. Array values and their arithmetic are rational. "
                + "Nat.div(a,b) is natural-number quotient, and Nat.sub(a,b)=max(a-b,0) is truncated natural subtraction. "
                + "The notation (k:Q) denotes the canonical rational image of k; Q and N denote the rational and natural numbers. "
                + "ite(P,a,b) denotes a if P holds and b otherwise. These index operations are distinct from rational subtraction and division.")),
            Node("T", "The literal rational recursion", ArrayDefinition(),
                "The map T:N x N -> Q is defined by lexicographic recursion on (n,k), decreasing the row before the column. "
                + "Column zero is separately set to zero. Every row has T(n,1)=1; the initial row has T(0,2)=1 and T(0,k)=0 for k>=3. "
                + "For m>=0 and k>=2 the odd recursion reads T(2m+1,k)=k*T(m,k)+T(m,k-1). "
                + "For m>=1 and k>=2 the even recursion subtracts (T(2m,k-1)+T(m,k-1))/(k-1) from k*T(m,k)+T(m,k-1). "
                + "Here the coefficients k and k-1 and the displayed division are rational. Recursive column indices use Nat.sub. "
                + "Every column used by these positive-domain recurrences is at least one, so their values are independent of the zero-column convention. "
                + "The definition uses the source scalar recursion and initial values, without assuming the block identity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T_one", "First column",
                All("n", Eqn(Call("T", V("n"), D(1)), D(1))),
                "The first column is one for every natural row, including row zero.",
                DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("T_odd", "Odd row recurrence", ParityRecurrence(even: false),
                "For every natural parent row and every column at least two, the odd row uses the two indicated parent entries.",
                DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("T_even", "Positive even row recurrence", ParityRecurrence(even: true),
                "For a positive parent row and a column at least two, subtract the rational correction using the preceding even-row and parent entries.",
                DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("g", "The dyadic valuation", All("n", Eqn(Call("g", V("n")), Call("padicValNat", D(2), V("n")))),
                "The map g:N -> N is padicValNat 2. For n>0 it is the exponent of the highest power of two dividing n, OEIS A007814(n). "
                + "The natural-valued convention at zero is g(0)=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("h", "The natural parent index", All("n", Eqn(Call("h", V("n")),
                NatDiv(NatSub(NatDiv(V("n"), Pow(D(2), Call("g", V("n")))), D(1)), D(2)))),
                "The map h:N -> N first takes the natural quotient n/2^g(n), then subtracts one with natural monus, then takes the natural quotient by two. "
                + "In particular h(0)=0. For positive n the quotient by 2^g(n) is exact and odd, and n=2^g(n)*(2*h(n)+1). "
                + "Thus h(n)=A025480(n-1) on the source domain; no integer-floor expression with a negative numerator is used at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dyadic_index", "Exact positive-row decomposition",
                All("n", Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("n")),
                    Eqn(V("n"), Mul(Pow(D(2), Call("g", V("n"))), Add(Mul(D(2), Call("h", V("n"))), D(1)))))),
                "For every positive natural n, n=2^g(n)*(2*h(n)+1). The proof uses the exact power-of-two valuation and odd quotient. "
                + "This source-owner helper is consumed by the block theorem and by the row-edge induction; no claim is made at zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("dyadic_extended_stirling_block", "The complete dyadic block identity", Result(),
                "For every n>=1 and k>=2, with no upper bound on either index, this is Kurkov's final FORMULA conjecture in A358612. "
                + "All powers have natural exponents and rational bases. The base (k:Q)-1 is parenthesized; the index Nat.sub(k,1) is a natural number. "
                + "The proof first establishes the same identity at row 2^r*(2*h+1) for all natural r and h by induction on r, "
                + "with an inner induction on k in the even step. The case k=2 uses the constant first column, and the case r=0 uses the odd recursion. "
                + "The valuation decomposition then identifies the row with n. This includes g(n)=0 and h(n)=0. "
                + "The proof is a derivation in this repository; the assertion and its attribution are Kurkov's. "
                + "Integrality, row-edge values and the separate transform conjectures are outside this statement.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("dyadic-extended-stirling-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Cast(Formula f) => P(Seq(f, Colon, Q()));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula NatDiv(Formula a, Formula b) => Qualified("Nat", "div", a, b);
    private static Formula NatSub(Formula a, Formula b) => Qualified("Nat", "sub", a, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula All(string name, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N(), body);
    private static Formula ArrayDefinition()
    {
        var n = V("n"); var k = V("k"); var half = NatDiv(n, D(2)); var prev = NatSub(k, D(1));
        var ordinary = Add(Mul(Cast(k), Call("T", half, k)), Call("T", half, prev));
        var correction = new Formula.Fraction(P(Add(Call("T", n, prev), Call("T", half, prev))), P(Sub(Cast(k), D(1))));
        var step = Sub(P(ordinary), Call("ite", Eqn(new Formula.Modulo(n, D(2)), D(0)), correction, D(0)));
        return All("n", All("k", Eqn(Call("T", n, k),
            Call("ite", Eqn(k, D(0)), D(0), Call("ite", Eqn(k, D(1)), D(1),
                Call("ite", Eqn(n, D(0)), Call("ite", Eqn(k, D(2)), D(1), D(0)), step))))));
    }
    private static Formula ParityRecurrence(bool even)
    {
        var m = V("m");
        var k = V("k");
        var prev = NatSub(k, D(1));
        var evenRow = Mul(D(2), m);
        var parentTerms = Add(Mul(Cast(k), Call("T", m, k)), Call("T", m, prev));
        var equality = even
            ? Eqn(Call("T", evenRow, k), Sub(parentTerms,
                new Formula.Fraction(Add(Call("T", evenRow, prev), Call("T", m, prev)), Sub(Cast(k), D(1)))))
            : Eqn(Call("T", Add(evenRow, D(1)), k), parentTerms);
        var columnGuard = Imp(Leq(D(2), k), equality);
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m);
        return All("m", All("k", even ? Imp(positive, columnGuard) : columnGuard));
    }
    private static Formula Result()
    {
        var n = V("n"); var k = V("k"); var g = Call("g", n); var h = Call("h", n);
        var rhs = Add(Mul(Pow(Sub(Cast(k), D(1)), g), Call("T", h, NatSub(k, D(1)))),
            Mul(Pow(Cast(k), Add(g, D(1))), Call("T", h, k)));
        return All("n", All("k", Imp(Leq(D(1), n), Imp(Leq(D(2), k), Eqn(Call("T", n, k), rhs)))));
    }
}
