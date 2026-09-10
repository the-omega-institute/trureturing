using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class AbsoluteReciprocalSquareShiftParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a384267");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolute reciprocal-square series satisfies conjecture C.1 of OEIS A384267.",
        H("Absolute Reciprocal-Square Shift Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a384267 defines a(n) as the "
                + "absolute value of the coefficient of x^n in 1+x/A(x)^2, where A "
                + "is its generating series. Conjecture C.1 states the binomial-quotient "
                + "congruence at every positive index.")),
            Paragraph(Text("Indices and binomial coefficients are natural numbers; "
                + "index subtraction is natural subtraction. The function div is natural "
                + "integer division, int is the natural-to-integer cast, and mod is "
                + "integer remainder. The coefficients a(n) are integers. A denotes "
                + "generatingSeries, P(n) denotes its local approximations, and mk "
                + "constructs a series from a coefficient function. The imported "
                + "absSeries from AbsoluteReciprocalSquareParity takes absolute values "
                + "coefficientwise. The expression invOfUnit(B,1) is the formal unit "
                + "inverse with prescribed constant coefficient one. T denotes the "
                + "integer generatingSeries from StripThreeTernaryCatalanParity. "
                + "The map pi is Int.castRingHom(ZMod(2)); map(pi,B) applies it to "
                + "each coefficient. The operator expand(2,B) substitutes X^2 for X.")),
            Node("a", "The stabilized coefficient sequence", SequenceFormula(),
                "Multiplication by X makes the reciprocal-square step increase "
                + "coefficient agreement by one degree. The diagonal coefficients "
                + "therefore stabilize under the displayed iteration.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The series has coefficient a(n) at degree n.", DescribeRole.Definition),
            Node("generating_equation", "The defining equation and normalization",
                Disp(Conjunction(Equal(Call("constantCoeff", A()), D(1)), Equation(A()))),
                "Agreement with every finite approximation gives the fixed-point "
                + "equation. Every approximation has constant coefficient one."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "The difference of two unit inverses is controlled by the difference "
                + "of their original series. Induction on the degree of coefficient "
                + "agreement then identifies any normalized solution with A."),
            Node("mod_two_identity", "The shifted ternary Catalan series",
                Disp(Equal(Reduce(A()), Add(D(1),
                    Mul(X(), Call("expand", D(2), Reduce(T())))))),
                "Absolute values disappear modulo two. Multiplying the reduced "
                + "equation by A^2 gives F^3=F^2+X for F=map(pi,A). Thus U=F+1 "
                + "satisfies U=X+U^3 with zero constant coefficient. The imported "
                + "strip3_mod_two and generating_equation show that map(pi,T) "
                + "satisfies the ternary Catalan equation, so V=X expand(2,map(pi,T)) "
                + "also satisfies V=X+V^3. The factor 1-U^2-UV-V^2 has constant "
                + "coefficient one; cancellation in the difference of the two cubic "
                + "equations proves U=V."),
            Node("a_zero", "The constant coefficient",
                Disp(Equal(Call("a", D(0)), D(1))),
                "The normalization of A gives a(0)=1."),
            Node("ternary_dvd", "Exact binomial division", DivisibilityFormula(),
                "The integers n and 3n-1 are coprime. The standard identity "
                + "(3n-1) choose(3n-2,n-1)=n choose(3n-1,n) therefore proves "
                + "the asserted divisibility."),
            Node("ternary_div_odd", "The quotient at odd indices", OddFormula(),
                "Exact division and cancellation give n times the quotient equal "
                + "to choose(3n-2,n-1). Substituting n=2r+1 gives the displayed equality."),
            Node("ternary_div_even", "The quotient at positive even indices", EvenFormula(),
                "Since 6r-1 is odd, exact division preserves parity. Lucas reduction "
                + "sends choose(6r-1,2r) to choose(3r-1,r) modulo two. The identity "
                + "3 choose(3r-1,r)=2 choose(3r,r), valid for r positive, makes "
                + "this last coefficient even."),
            Node("hanna_conjecture", "Hanna's conjecture C.1", HannaFormula(),
                "The series identity gives zero at positive even indices and "
                + "choose(3r,r) modulo two at index 2r+1, using the imported "
                + "mod_two_identity for T. The even quotient is even. At odd "
                + "indices, multiplication by 2r+1 preserves parity, and Lucas "
                + "reduction sends choose(6r+1,2r) to choose(3r,r). These two "
                + "cases establish the stated congruence for every positive n.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a384267-absolute-reciprocal-square-shift-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a384267-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula A() => F.Id("A");
    private static Formula T() => F.Id("T");
    private static Formula X() => F.Id("X");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Divides(Formula divisor, Formula value) => Seq(divisor, Sp, Mid, Sp, value);
    private static Formula Reduce(Formula series) => Call("map", F.Id("pi"), series);
    private static Formula Step(Formula series) => Call("absSeries",
        Add(D(1), Mul(X(), Call("invOfUnit", Power(series, D(2)), D(1)))));
    private static Formula Equation(Formula series) => Equal(series, Step(series));
    private static Formula Quotient(Formula top, Formula bottom, Formula divisor) =>
        Call("div", Call("choose", top, bottom), divisor);

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(Call("P", Add(n, D(1))), Step(Call("P", n)))),
            Seq(Bound("n", Naturals()), Equal(Call("a", n),
                Call("coeff", n, Call("P", Add(n, D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula DivisibilityFormula()
    {
        Formula n = F.Id("n");
        Formula top = Subtract(Mul(D(3), n), D(1));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, n), Divides(top, Call("choose", top, n)))));
    }

    private static Formula OddFormula()
    {
        Formula r = F.Id("r");
        Formula six = Add(Mul(D(6), r), D(2));
        Formula two = Add(Mul(D(2), r), D(1));
        return Disp(Seq(Bound("r", Naturals()), Equal(Quotient(six, two, six),
            Quotient(Add(Mul(D(6), r), D(1)), Mul(D(2), r), two))));
    }

    private static Formula EvenFormula()
    {
        Formula r = F.Id("r");
        Formula top = Subtract(Mul(D(6), r), D(1));
        return Disp(Seq(Bound("r", Naturals()), Implication(Seq(D(0), Sp, Lt, Sp, r),
            Divides(D(2), Quotient(top, Mul(D(2), r), top)))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula top = Subtract(Mul(D(3), n), D(1));
        return Disp(Seq(Bound("n", Naturals()), Implication(Seq(D(1), Sp, Le, Sp, n),
            Equal(new Formula.Modulo(Call("a", n), D(2)),
                new Formula.Modulo(Call("int", Quotient(top, n, top)), D(2))))));
    }
}
