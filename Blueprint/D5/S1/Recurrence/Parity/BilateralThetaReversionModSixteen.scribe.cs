using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class BilateralThetaReversionModSixteenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2022a355872");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bilateral theta equation of OEIS A355872 implies Hanna's three congruences.",
        H("Bilateral Theta Reversion Modulo Sixteen"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2022a355872 defines A by the bilateral "
                + "equation x = sum over integer j of (-x)^(j^2) A(x)^((j-1)^2). "
                + "Its three conjectures concern a(n) modulo four and a(2n-1), a(2n) "
                + "modulo eight, for every positive n.")),
            Paragraph(Text("Here A denotes generatingSeries, an integer formal power series "
                + "with indeterminate X. The indices m, n, N, d are natural numbers; j is "
                + "an integer. The function natAbs takes an integer's absolute value as a "
                + "natural number. Subtraction in natural indices is truncated subtraction; "
                + "j-1 and -N in the bilateral window are integer expressions. The operator "
                + "mod denotes remainder. The operator coeff extracts a coefficient, mk "
                + "constructs a series from its coefficients, and invOfUnit denotes the "
                + "formal inverse with the specified unit constant coefficient.")),
            Node("bilateralTerm", "An integer-indexed summand", TermFormula(),
                "Natural absolute-value squares give the nonnegative exponents in the "
                + "bilateral equation.", DescribeRole.Definition),
            Node("c", "The stabilized integer coefficients", CoefficientFormula(),
                "The auxiliary P(d) is approximation at depth d. The auxiliary T(B) is "
                + "tail(B), whose coefficient at N omits indices zero and one from W(N). "
                + "Each remaining summand contains a positive power of X, so one iteration "
                + "improves coefficient agreement by one degree. The coefficient at m "
                + "therefore stabilizes at depth m+1.", DescribeRole.Definition),
            Node("a", "The OEIS indexing", SequenceFormula(),
                "The sequence selects degree 4n-3 of A. The conjectures use n at least one; "
                + "the definition itself uses natural subtraction for every n.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", F.Id("c")))),
                "The coefficient function of A is c.", DescribeRole.Definition),
            Node("generating_equation", "The bilateral generating equation", EquationFormula(),
                "The stabilized iteration satisfies A=2X-T(A). At every positive degree "
                + "the window contains zero and one, whose summands are A and -X. "
                + "Restoring them gives the stated equation; the constant coefficient is zero."),
            Node("generating_unique", "Uniqueness of the zero-constant solution", UniqueFormula(),
                "Isolating the same two indices turns every solution into a fixed point "
                + "of the same operator. Induction on degree proves agreement of all "
                + "coefficients and hence equality of the series."),
            Node("bilateralTerm_coeff_eq_zero", "The coefficient order bound", OrderFormula(),
                "Zero constant coefficient makes F divisible by X. Raising this divisibility "
                + "to the indicated powers shows that a summand is divisible by X to the "
                + "sum of the two squares. Its lower coefficients vanish. An index outside "
                + "the window [-N,N] has j^2>N, so the finite window is exact."),
            Node("support_one_mod_four", "Support in one residue class", SupportFormula(),
                "Multiplication adds support residues and taking powers multiplies them. "
                + "The identity j^2+(j-1)^2 congruent to one modulo four makes every "
                + "bilateral summand preserve support in that residue class. Iteration "
                + "and coefficient stabilization transfer this support to A."),
            Node("mod_sixteen_identity", "The full reduction modulo sixteen", ModSixteenFormula(),
                "Over ZMod(16), put S=2X invOfUnit(1+X^4,1). Then S^4=0. "
                + "Every term of T(S) except index two contains at least the fourth power "
                + "of S and vanishes. Thus T(S)=X^4 S. The inverse identity gives "
                + "S+X^4 S=2X, so S is a fixed point. Reduction of A commutes with the "
                + "finite-window operator; degree contraction identifies it with S. "
                + "In the formula map applies the canonical integer-to-ZMod(16) ring "
                + "homomorphism coefficientwise; intCastRingHom denotes Int.castRingHom. "
                + "The right side is over ZMod(16)."),
            Node("hanna_conjecture", "Hanna's congruence modulo four", HannaFormula(),
                "Coefficient comparison in S+X^4 S=2X gives coefficient 2(-1)^k at "
                + "degree 4k+1. With k=n-1, reduction modulo four gives two for either "
                + "sign.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a355872-bilateral-theta-reversion-mod-sixteen"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_mod_eight", "Hanna's two congruences modulo eight", HannaEightFormula(),
                "At index 2n-1 the exponent k is even, so the coefficient is two "
                + "modulo sixteen. At index 2n it is odd, so the coefficient is minus "
                + "two modulo sixteen. Reduction modulo eight gives two and six.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a355872-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula SquareAbs(Formula j) => Power(Call("natAbs", j), D(2));
    private static Formula Window(Formula n) => Call("Icc", Seq(Minus, n), n);
    private static Formula SumOver(string index, Formula set, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(index), Sp, InMacro, Sp, set)), Sp,
        Parenthesized(body));
    private static Formula Coeff(Formula n, Formula b) => Call("coeff", n, b);
    private static Formula Term(Formula b, Formula j) => Call("bilateralTerm", b, j);

    private static Formula TermFormula()
    {
        Formula b = F.Id("F");
        Formula j = F.Id("j");
        return Disp(Seq(Bound("F", Series()), Bound("j", Integers()), Equal(Term(b, j),
            Mul(Power(Parenthesized(Seq(Minus, X())), SquareAbs(j)),
                Power(b, SquareAbs(Subtract(j, D(1))))))));
    }

    private static Formula CoefficientFormula()
    {
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula n = F.Id("N");
        Formula b = F.Id("B");
        Formula j = F.Id("j");
        Formula indices = Call("erase", Call("erase", Call("W", n), D(0)), D(1));
        return Disp(new Formula.Aligned([
            Seq(Bound("m", Naturals()), Equal(Call("c", m), Coeff(m, Call("P", Add(m, D(1)))))),
            Equal(Call("P", D(0)), D(0)),
            Seq(Bound("d", Naturals()), Equal(Call("P", Add(d, D(1))),
                Subtract(Mul(D(2), X()), Call("T", Call("P", d))))),
            Seq(Bound("N", Naturals()), Equal(Call("W", n), Window(n))),
            Seq(Bound("B", Series()), Bound("N", Naturals()), Equal(Coeff(n, Call("T", b)),
                SumOver("j", indices, Coeff(n, Term(b, j)))))
        ]));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()),
            Equal(Call("a", n), Call("c", Subtract(Mul(D(4), n), D(3))))));
    }

    private static Formula Equation(Formula b)
    {
        Formula n = F.Id("N");
        Formula j = F.Id("j");
        return Seq(Bound("N", Naturals()), Equal(Coeff(n, X()),
            SumOver("j", Window(n), Coeff(n, Term(b, j)))));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(0)), Equation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula OrderFormula()
    {
        Formula b = F.Id("F");
        Formula n = F.Id("N");
        Formula j = F.Id("j");
        Formula order = Add(SquareAbs(j), SquareAbs(Subtract(j, D(1))));
        return Disp(Seq(Bound("F", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Seq(Bound("N", Naturals()), Bound("j", Integers()),
                    Implication(Seq(n, Sp, Lt, Sp, order), Equal(Coeff(n, Term(b, j)), D(0)))))));
    }

    private static Formula SupportFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(Bound("m", Naturals()),
            Implication(Seq(new Formula.Modulo(m, D(4)), Sp, Neq, Sp, D(1)),
                Equal(Call("c", m), D(0)))));
    }

    private static Formula ModSixteenFormula() => Disp(Equal(
        Call("map", Call("intCastRingHom", Call("ZMod", D(1, 6))), A()),
        Mul(Mul(D(2), X()), Call("invOfUnit", Add(D(1), Power(X(), D(4))), D(1)))));

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n),
                Equal(new Formula.Modulo(Call("a", n), D(4)), D(2)))));
    }

    private static Formula HannaEightFormula()
    {
        Formula n = F.Id("n");
        Formula odd = Call("a", Subtract(Mul(D(2), n), D(1)));
        Formula even = Call("a", Mul(D(2), n));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n), Parenthesized(Conjunction(
                Equal(new Formula.Modulo(odd, D(8)), D(2)),
                Equal(new Formula.Modulo(even, D(8)), D(6)))))));
    }
}
