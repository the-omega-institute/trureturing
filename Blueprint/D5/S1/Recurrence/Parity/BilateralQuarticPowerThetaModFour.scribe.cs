using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class BilateralQuarticPowerThetaModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.";
    private const string ThetaModule = "D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a379204");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bilateral equation of OEIS A379204 implies Hanna's parity and square-shift conjectures.",
        H("Bilateral Quartic Powers Modulo Four"),
        Blocks(
            Paragraph(Text("The entry hanna2024a379204 defines A by 1/x equal to the sum "
                + "over integer n of A(x)^n times (A(x)^n+4)^(n+1). Hanna conjectures "
                + "that a(n) is even for n greater than one, and that its remainder "
                + "modulo four is two exactly when n=(k-1)^2+1 for a natural k greater "
                + "than one. The complete mod-four classification below implies "
                + "the evenness conjecture.")),
            Paragraph(Text("Here generatingSeries is an integer formal power series and X "
                + "is its indeterminate. The indices N, d, k, and the argument of a are "
                + "natural numbers; the argument n of bilateralTerm is an integer. "
                + "The operator toNat truncates an integer below zero, natAbs is its "
                + "natural absolute value, and intCast embeds a natural number into "
                + "the integers. Subtraction in natural exponents and k-1 is truncated. "
                + "The operator coeff extracts a coefficient, mk constructs a series "
                + "from its coefficient function, and invOfUnit denotes the formal "
                + "inverse with the specified unit constant coefficient. The operator "
                + "mod is integer remainder; map applies a ring homomorphism to every "
                + "coefficient, and intCastRingHom denotes Int.castRingHom.")),
            Paragraph(Text("The imported thetaSeries belongs to "), Ref(ThetaModule),
                Text(". Its constant coefficient is one; its other coefficients are "
                + "two at positive square degrees and zero elsewhere, as stated by "
                + "coeff_thetaSeries.")),
            Node("bilateralTerm", "The ordinary-series bilateral terms", TermFormula(),
                "For n=-r with r at least two, factoring powers of A gives the "
                + "displayed nonnegative exponent and unit inverse. The index -1 is "
                + "the Laurent term A^(-1). Multiplication of the equation by X*A "
                + "absorbs that term into the isolated X, so bilateralTerm(A,-1)=0.",
                DescribeRole.Definition),
            Node("a", "The stabilized coefficient sequence", SequenceFormula(),
                "The auxiliary P is the degree approximation. Its initial value is "
                + "zero, and the displayed iteration preserves zero constant coefficient. "
                + "Products, powers, and inverses of the unit denominators preserve "
                + "agreement below degree d. The outer X improves agreement to degree "
                + "d+1, so the diagonal coefficient stabilizes.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The exact finite-window equation", EquationFormula(),
                "Coefficient stabilization gives a fixed point of the displayed "
                + "finite-window operator. Its constant coefficient is zero and its "
                + "linear coefficient is one. The order bound below justifies the "
                + "window as the coefficientwise meaning of the bilateral equation "
                + "after multiplication by X*A."),
            Node("generating_unique", "Uniqueness of the zero-constant solution", UniqueFormula(),
                "Every solution is a fixed point of the same operator. For two unit "
                + "denominators U and V, their inverse difference is "
                + "-inv(U)*(U-V)*inv(V), so inversion preserves coefficient agreement. "
                + "Induction using the outer X proves equality of every coefficient."),
            Node("bilateralTerm_coeff_eq_zero", "The order and window bounds", OrderFormula(),
                "Zero constant coefficient makes A divisible by X. Each term is "
                + "therefore divisible by the displayed power of X. An index outside "
                + "[-N-2,N] makes this power greater than N, so both the order "
                + "criterion and the outside-window criterion force a zero coefficient."),
            Node("mod_two_identity", "The series modulo two",
                Disp(Equal(Reduce(A(), 2), X())),
                "Modulo four, A times the term at m and A times the term at -m-2 "
                + "both equal A^((m+1)^2). The central term is zero. Pairing the "
                + "whole finite interval therefore gives twice a finite sum of square "
                + "powers. Mapping this identity to ZMod(2) removes the sum and gives A=X."),
            Node("mod_four_identity", "The theta identity modulo four",
                Disp(Equal(Reduce(A(), 4), Mul(X(), Reduce(ThetaSeries(), 4)))),
                "Equality of integer series modulo two implies equality of their "
                + "doubles modulo four. Apply this to the finite sums of square powers "
                + "of A and X. The paired fixed-point equation becomes X times one "
                + "plus twice the square-power sum. At each degree, at most one "
                + "positive square root contributes, giving the imported theta coefficient."),
            Node("hanna_conjecture_mod_four", "The square-shift characterization", ModFourFormula(),
                "For n at least one, coefficient comparison gives remainder two "
                + "exactly when n-1 is a positive square, equivalently n=(k-1)^2+1 "
                + "with k greater than one. The remainder-zero clause also requires "
                + "n greater than one, because the linear coefficient is one. The "
                + "remainder-two biconditional proves the second conjecture in hanna2024a379204."),
            Node("hanna_conjecture", "Hanna's evenness conjecture", ParityFormula(),
                "For n greater than one, the mod-four classification gives either "
                + "remainder two or remainder zero. Both imply divisibility by two, "
                + "proving the first conjecture in hanna2024a379204.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a379204-bilateral-quartic-power-theta-mod-four"),
                    ResolutionKind.Proved))),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create(ThetaModule))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a379204-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => Named("generatingSeries");
    private static Formula ThetaSeries() => Named("thetaSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LessEqual(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Lor, Sp, Parenthesized(right));
    private static Formula Biconditional(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp,
        Named("else"), Sp, no);
    private static Formula Coeff(Formula n, Formula b) => Call("coeff", n, b);
    private static Formula Term(Formula b, Formula n) => Call("bilateralTerm", b, n);
    private static Formula Window(Formula n) => Call("Icc",
        Subtract(Negative(Call("intCast", n)), D(2)), Call("intCast", n));
    private static Formula SumOver(string index, Formula set, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(index), Sp, InMacro, Sp, set)), Sp,
        Parenthesized(body));
    private static Formula Reduce(Formula series, byte modulus) =>
        Call("map", Call("intCastRingHom", Call("ZMod", D(modulus))), series);
    private static Formula NegativeExponent(Formula n) =>
        Subtract(Power(Parenthesized(Subtract(Call("natAbs", n), D(1))), D(2)), D(1));

    private static Formula TermFormula()
    {
        Formula b = F.Id("A");
        Formula n = F.Id("n");
        Formula r = Call("natAbs", n);
        Formula m = Call("toNat", n);
        Formula positive = Mul(Power(b, m),
            Power(Parenthesized(Add(Power(b, m), D(4))), Add(m, D(1))));
        Formula negative = Mul(Power(b, NegativeExponent(n)),
            Power(Call("invOfUnit", Add(D(1), Mul(D(4), Power(b, r))), D(1)),
                Subtract(r, D(1))));
        return Disp(Seq(Bound("A", Series()), Bound("n", Integers()), Equal(Term(b, n),
            Parenthesized(IfThenElse(LessEqual(D(0), n), positive,
                Parenthesized(IfThenElse(Equal(n, Negative(D(1))), D(0), negative)))))));
    }

    private static Formula RightSide(Formula b, Formula n) => Add(X(),
        Mul(Mul(X(), b), SumOver("j", Window(n), Term(b, F.Id("j")))));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula degree = F.Id("N");
        Formula p = Call("P", d);
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", n),
                Coeff(n, Call("P", Add(n, D(1)))))),
            Equal(Call("P", D(0)), D(0)),
            Seq(Bound("d", Naturals()), Equal(Call("P", Add(d, D(1))),
                Call("mk", Parenthesized(Seq(degree, Colon, Sp, Naturals(), Sp, Mapsto, Sp,
                    Coeff(degree, RightSide(p, degree)))))))
        ]));
    }

    private static Formula Equation(Formula b)
    {
        Formula n = F.Id("N");
        return Seq(Bound("N", Naturals()), Equal(Coeff(n, b), Coeff(n, RightSide(b, n))));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(0)), Conjunction(
            Equal(Coeff(D(1), A()), D(1)), Equation(A()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula OrderFormula()
    {
        Formula b = F.Id("A");
        Formula degree = F.Id("N");
        Formula n = F.Id("n");
        Formula order = Parenthesized(IfThenElse(LessEqual(D(0), n),
            Call("toNat", n), NegativeExponent(n)));
        Formula outside = Not(Seq(n, Sp, InMacro, Sp, Window(degree)));
        return Disp(Seq(Bound("A", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Seq(Bound("N", Naturals()), Bound("n", Integers()),
                    Implication(Parenthesized(Disjunction(Less(degree, order), outside)),
                        Equal(Coeff(degree, Term(b, n)), D(0)))))));
    }

    private static Formula ShiftedSquare(Formula n)
    {
        Formula k = F.Id("k");
        return Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(Conjunction(Less(D(1), k),
                Equal(n, Add(Power(Parenthesized(Subtract(k, D(1))), D(2)), D(1))))));
    }

    private static Formula ModFourFormula()
    {
        Formula n = F.Id("n");
        Formula remainder = new Formula.Modulo(Call("a", n), D(4));
        Formula support = ShiftedSquare(n);
        return Disp(Seq(Bound("n", Naturals()),
            Implication(LessEqual(D(1), n), Parenthesized(Conjunction(
                Biconditional(Equal(remainder, D(2)), support),
                Biconditional(Equal(remainder, D(0)),
                    Conjunction(Less(D(1), n), Not(support))))))));
    }

    private static Formula ParityFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Less(D(1), n), Call("Even", Call("a", n)))));
    }
}
