using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class BilateralQuarterDoubleShiftThetaModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/BilateralQuarterDoubleShiftThetaModFour.";
    private const string ThetaModule = "D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2023a363184");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer solution of the A363184 bilateral equation is theta_3(x^2) modulo four.",
        H("Bilateral Quarter-Double-Shift Theta Congruence"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entry hanna2023a363184, dated May 20, 2023, "
                + "defines A by 4 = sum over integer n of (-1)^n*x^n*(4*A(x)+x^(2*n-1))^(n+1). "
                + "It conjectures the theta_3(x^2) congruence and the doubled-square classification "
                + "of the positive coefficients modulo four.")),
            Paragraph(Text("The terms at n=0 and n=-1 contain opposite Laurent monomials "
                + "x^(-1) and -x^(-1). They cancel, leaving 4*A and zero respectively. "
                + "For n=-m-2 with m natural, factoring the negative power gives the "
                + "displayed negativeTerm. The formal equation below uses exact finite "
                + "coefficient windows; it does not assert a bilateral infinite-sum "
                + "operation on formal power series.")),
            Paragraph(Text("All series are over the integers unless mapped to ZMod(4). "
                + "The indices m, n in a(n), N, and d are natural; the index n in "
                + "bilateralTerm is an integer. The function toNat sends negative "
                + "integers to zero. Subtraction after toNat is natural truncated "
                + "subtraction; the window endpoints and -n-2 use integer arithmetic. "
                + "The operations div and mod are integer division and remainder on the integers; on natural-number arguments, as in n div 2, they are natural division and remainder. "
                + "The operator mk builds a series from coefficients, and invOfUnit "
                + "is the formal unit inverse. The symbols positiveTerm, negativeTerm, "
                + "R, and P below are the private auxiliary definitions.")),
            Paragraph(Text("The imported thetaSeries and its coefficient formula are from "),
                Ref(ThetaModule + ".thetaSeries"), Text(" and "),
                Ref(ThetaModule + ".coeff_thetaSeries"),
                Text(". Its constant coefficient is one, and each positive square "
                    + "coefficient is two; all other coefficients are zero. The operator "
                    + "expand(2,thetaSeries) replaces X by X^2, so its positive support "
                    + "consists exactly of n=2*k^2 with k>0.")),
            Node("bilateralTerm", "The reindexed bilateral terms", TermFormula(),
                "Positive index m+1 and negative index -m-2 use nonnegative exponents "
                + "and an inverse whose constant coefficient is one.", DescribeRole.Definition),
            Node("bilateralTerm_coeff_eq_zero", "Exact finite windows", OrderFormula(),
                "Both terms indexed by m contain at least X^(m+1). Every integer "
                + "index outside [-N-2,N] therefore has zero coefficient at degree N."),
            Node("a", "The stabilized integer coefficients", SequenceFormula(),
                "Each positive-negative pair vanishes at A=0. Differences of powers "
                + "and the unit-inverse difference identity show that every pair is "
                + "divisible by four. Thus the displayed division is exact over the "
                + "integers. Agreement below degree d improves to agreement below "
                + "degree d+1 under the iteration, so the selected coefficients stabilize.",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The coefficient function of generatingSeries is a.", DescribeRole.Definition),
            Node("generating_equation", "The defining bilateral equation", EquationFormula(),
                "The stabilized series is fixed by the integral iteration. Rejoining "
                + "the pairs restores the finite integer window. Its extra positive "
                + "endpoint has zero coefficient, and the index-zero term gives 4*A."),
            Node("generating_unique", "Uniqueness of the solution", UniqueFormula(),
                "Every series satisfying the same finite-window equation is fixed "
                + "by the iteration. Degree contraction proves equality at every coefficient."),
            Node("a_zero", "The constant coefficient", Disp(Equal(Call("a", D(0)), D(1))),
                "Every paired term has positive order, so the iteration has constant coefficient one."),
            Node("cancellation_identity", "Cancellation over the integers", CancellationFormula(),
                "Modulo sixteen, (4*A)^2 vanishes. Expanding each pair leaves its "
                + "linear terms, whose weighted finite sum telescopes to eight times "
                + "A times the positive doubled-square support series. Multiplication by eight "
                + "removes the alternating signs modulo sixteen. Hence the difference "
                + "between the remainder and 4*A*(expand(2,thetaSeries)-1) is 16*Q with integral "
                + "Q. The generating equation gives 4=4*(A*expand(2,thetaSeries)+4*Q); cancelling "
                + "the nonzero factor four in the integer series ring gives the statement."),
            Node("mod_four_identity", "The series congruence", ModFourFormula(),
                "The reduction of expand(2,thetaSeries) is 1+2*S, where S indicates the positive "
                + "doubled squares. Its square is one over ZMod(4). Reducing the integer "
                + "cancellation identity and multiplying by this self-inverse series "
                + "identifies the reduction of generatingSeries."),
            Node("hanna_conjecture", "Hanna's A363184 conjecture", ConjectureFormula(),
                "At a positive index, the expanded theta coefficient is two exactly "
                + "at n=2*k^2 for k>0 and zero otherwise. Coefficient comparison and the "
                + "integer-cast remainder equivalence prove both biconditionals in "
                + "hanna2023a363184.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a363184-bilateral-quarter-double-shift-theta-mod-four"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_floor", "The nonsquare floor corollary", FloorFormula(),
                "If n=2*k^2 with k>0, natural division gives n div 2=k^2. "
                + "Thus a nonsquare floor excludes every doubled square, and the "
                + "zero biconditional gives the conclusion.")),
        [DocumentEdge.Dependency.Create(GidRef.Create(ThetaModule))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a363184-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => Named("generatingSeries");
    private static Formula Theta() => Call("expand", D(2), Named("thetaSeries"));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Sign(Formula exponent) => Power(Negative(D(1)), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Biconditional(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
            yes, Sp, Named("else"), Sp, no));
    private static Formula SumOver(string index, Formula set, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(index), Sp, InMacro, Sp, set)), Sp,
        Parenthesized(body));
    private static Formula Coeff(Formula n, Formula b) => Call("coeff", n, b);
    private static Formula Term(Formula b, Formula n) => Call("bilateralTerm", b, n);
    private static Formula Positive(Formula b, Formula m) => Call("positiveTerm", b, m);
    private static Formula NegativeTerm(Formula b, Formula m) => Call("negativeTerm", b, m);
    private static Formula Window(Formula n) => Call("Icc", Subtract(Negative(n), D(2)), n);
    private static Formula Approx(Formula d) => Call("P", d);
    private static Formula ModFour(Formula b) =>
        Call("map", Call("intCastRingHom", Call("ZMod", D(4))), b);

    private static Formula TermFormula()
    {
        Formula b = F.Id("A"), n = F.Id("n"), m = F.Id("m");
        Formula positive = Mul(Mul(Sign(Add(m, D(1))), Power(X(), Add(m, D(1)))),
            Power(Add(Mul(D(4), b), Power(X(), Add(Mul(D(2), m), D(1)))), Add(m, D(2))));
        Formula inverse = Call("invOfUnit",
            Add(D(1), Mul(Mul(D(4), b), Power(X(), Add(Mul(D(2), m), D(5))))), D(1));
        Formula negative = Mul(Mul(Sign(Add(m, D(2))),
            Power(X(), Add(Add(Mul(D(2), Power(m, D(2))), Mul(D(6), m)), D(3)))),
            Power(inverse, Add(m, D(1))));
        return Disp(new Formula.Aligned([
            Seq(Bound("A", Series()), Bound("n", Integers()), Equal(Term(b, n),
                IfThenElse(Equal(n, D(0)), Mul(D(4), b),
                    IfThenElse(Equal(n, Negative(D(1))), D(0),
                        IfThenElse(Seq(D(0), Sp, Lt, Sp, n),
                            Positive(b, Subtract(Call("toNat", n), D(1))),
                            NegativeTerm(b, Call("toNat", Subtract(Negative(n), D(2))))))))),
            Seq(Bound("A", Series()), Bound("m", Naturals()), Equal(Positive(b, m), positive)),
            Seq(Bound("A", Series()), Bound("m", Naturals()), Equal(NegativeTerm(b, m), negative))
        ]));
    }

    private static Formula OrderFormula()
    {
        Formula b = F.Id("A"), n = F.Id("n"), degree = F.Id("N");
        Formula outside = Seq(Parenthesized(Seq(n, Sp, Lt, Sp,
            Subtract(Negative(degree), D(2)))), Sp, Lor, Sp,
            Parenthesized(Seq(degree, Sp, Lt, Sp, n)));
        return Disp(Seq(Bound("A", Series()), Bound("N", Naturals()), Bound("n", Integers()),
            Implication(outside, Equal(Coeff(degree, Term(b, n)), D(0)))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), degree = F.Id("N"), b = F.Id("B"), m = F.Id("m");
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Coeff(n, Approx(Add(n, D(1)))))),
            Equal(Approx(D(0)), D(1)),
            Seq(Bound("d", Naturals()), Equal(Approx(Add(d, D(1))),
                Subtract(D(1), Call("mk", Lambda("N",
                    Call("div", Coeff(degree, Call("R", Approx(d))), D(4))))))),
            Seq(Bound("B", Series()), Bound("N", Naturals()), Equal(Coeff(degree, Call("R", b)),
                SumOver("m", Call("range", Add(degree, D(1))),
                    Coeff(degree, Add(Positive(b, m), NegativeTerm(b, m))))))
        ]));
    }

    private static Formula Equation(Formula b)
    {
        Formula degree = F.Id("N"), n = F.Id("n");
        return Seq(Bound("N", Naturals()), Equal(Coeff(degree, D(4)),
            Coeff(degree, SumOver("n", Window(degree), Term(b, n)))));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(1)), Equation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula CancellationFormula() => Disp(Seq(Exists, Sp, F.Id("Q"), Colon, Sp,
        Series(), Comma, Sp, Equal(D(1), Add(Mul(A(), Theta()), Mul(D(4), F.Id("Q"))))));

    private static Formula ModFourFormula() => Disp(Equal(ModFour(A()), ModFour(Theta())));

    private static Formula ConjectureFormula()
    {
        Formula n = F.Id("n"), remainder = new Formula.Modulo(Call("a", n), D(4));
        Formula square = DoubledSquare(n);
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n), Parenthesized(Conjunction(
                Biconditional(Equal(remainder, D(2)), square),
                Biconditional(Equal(remainder, D(0)), Seq(Neg, Sp, Parenthesized(square))))))));
    }

    private static Formula DoubledSquare(Formula n)
    {
        Formula k = F.Id("k");
        return Parenthesized(Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Conjunction(Seq(D(0), Sp, Lt, Sp, k), Equal(n, Mul(D(2), Power(k, D(2)))))));
    }

    private static Formula FloorFormula()
    {
        Formula n = F.Id("n");
        Formula nonsquare = Seq(Neg, Sp, Parenthesized(Call("IsSquare", Call("div", n, D(2)))));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n),
                Implication(nonsquare, Equal(new Formula.Modulo(Call("a", n), D(4)), D(0))))));
    }
}
