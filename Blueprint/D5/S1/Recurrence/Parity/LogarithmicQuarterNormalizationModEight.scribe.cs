using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class LogarithmicQuarterNormalizationModEightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396846");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A396846 repeat 1, 7, 5, 7 modulo eight.",
        H("Logarithmic Quarter Normalization Modulo Eight"),
        Blocks(
            Paragraph(Text("The second conjecture in hanna2026a396846 concerns the logarithmic "
                + "generating function with argument 1+x+Sum 4n a(n)x^n/(4n^2-1). "
                + "Its formal meaning is B H = X H', with constant coefficient of H equal "
                + "to one. The series with positive-degree coefficients a(n)/n and zero "
                + "constant coefficient is therefore the formal logarithm of H.")),
            Paragraph(Text("Indices are natural numbers, and subtraction in an index is "
                + "natural subtraction. The sequences a and c take integer values; their "
                + "values and natural indices are embedded in the rational numbers in rational "
                + "formulas. The expression 4n^2-1 uses ring subtraction. The notation "
                + "mod is integer remainder, range(n) is 0<=k<n, and Ico(r,n) is r<=k<n. "
                + "The operator mk constructs a formal series from its coefficient function; "
                + "mapInt applies the canonical integer-to-rational ring homomorphism. "
                + "The symbol X is the formal indeterminate in the indicated coefficient ring.")),
            Node("c", "Integral normalized coefficients", CFormula(),
                "The guarded recursion uses only smaller indices and sets c(0)=c(1)=0.",
                DescribeRole.Definition),
            Node("a", "The coefficient sequence", AFormula(),
                "The coefficient at one is one. All other coefficients are obtained by "
                + "multiplying c(n) by 4n^2-1; in particular a(0)=0.", DescribeRole.Definition),
            Node("c_recurrence", "The integral convolution recurrence", RecurrenceFormula(),
                "Removing the guards from the well-founded definition restricts the sum "
                + "to 2<=k<n. The coefficient of c(n) is one."),
            Node("a_eq", "The integral normalization", NormalizationFormula(),
                "For n>=2 the integer a(n) is (4n^2-1)c(n)."),
            Node("H", "The logarithm argument", HFormula(),
                "The constant and linear coefficients are one, and coefficient n>=2 is "
                + "4n c(n).", DescribeRole.Definition),
            Node("B", "The ordinary coefficient series", BFormula(),
                "The series B has coefficient a(n) at every natural index.", DescribeRole.Definition),
            Node("log_derivative_identity", "The formal logarithmic equation", IdentityFormula(),
                "Coefficient comparison separates the constant and linear factors in the "
                + "product B H. The remaining convolution is the defining recurrence for c; "
                + "together with a(n)=(4n^2-1)c(n), it equals n times coefficient n of H."),
            Node("coeff_H_rat", "The exact rational coefficient shape", RationalShapeFormula(),
                "For n>=2 the denominator 4n^2-1 is nonzero. Substituting the integral "
                + "normalization gives exactly the logarithm argument in hanna2026a396846."),
            Node("generating_unique", "Uniqueness among rational solutions", UniqueFormula(),
                "Strong induction compares coefficient n of the logarithmic equations. "
                + "All interior convolution terms agree by the induction hypothesis. "
                + "Clearing the nonzero denominator leaves equality of the nth coefficients."),
            Node("all_odd", "Every positive-index coefficient is odd", OddFormula(),
                "The recurrence makes c(n) congruent to a(n-1) modulo two, and its "
                + "normalizing factor 4n^2-1 is odd. Induction starts at a(1)=1."),
            Node("hanna_conjecture", "The second A396846 conjecture", ConjectureFormula(),
                "Oddness makes each normalized convolution term congruent to its index "
                + "modulo two. Multiplication by four reduces the convolution modulo eight "
                + "to four times the sum of indices 2<=k<n. This is four for n congruent "
                + "to zero or one modulo four and zero otherwise. Induction through the "
                + "four index classes yields the asserted repeating residues.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396846-logarithmic-quarter-normalization-mod-eight"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396846-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula X() => F.Id("X");
    private static Formula HSeries() => F.Id("H");
    private static Formula BSeries() => F.Id("B");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
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
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula AtLeast(Formula value, Formula bound) => Seq(bound, Sp, Le, Sp, value);
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(Seq(
        Named("if"), Sp, Parenthesized(test), Sp, Named("then"), Sp, yes,
        Sp, Named("else"), Sp, no));
    private static Formula FunctionType(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula LambdaN(Formula body) => Parenthesized(Seq(N(), Sp, Mapsto, Sp, body));
    private static Formula Coefficient(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula C(Formula index) => Call("c", index);
    private static Formula Factor(Formula index) =>
        Subtract(Mul(D(4), Power(Parenthesized(index), D(2))), D(1));
    private static Formula Weight(Formula index, Formula value) =>
        Conditional(Equal(index, D(1)), D(1), Mul(Parenthesized(Factor(index)), value));
    private static Formula Sum(Formula set, Formula summand) => Seq(
        new Formula.Subscript(F.Sum, Seq(K(), Sp, InMacro, Sp, set)), Sp, Parenthesized(summand));
    private static Formula RationalTerm(Formula index, Formula value) =>
        Mul(new Formula.Fraction(Mul(D(4), index), Factor(index)), value);
    private static Formula Equation(Formula b, Formula h, Formula ring) =>
        Equal(Mul(b, h), Mul(X(), Call("derivative", ring, h)));

    private static Formula CFormula()
    {
        Formula prior = Subtract(N(), D(1));
        Formula other = Subtract(N(), K());
        Formula term = Mul(Mul(K(), C(K())), Weight(other, C(other)));
        Formula guarded = Conditional(Conjunction(AtLeast(K(), D(2)), Seq(K(), Sp, Lt, Sp, N())),
            term, D(0));
        return Disp(new Formula.Aligned([
            Seq(Named("c"), Colon, Sp, FunctionType(Naturals(), Integers())),
            Seq(Bound("n", Naturals()), Equal(C(N()), Conditional(AtLeast(N(), D(2)),
                Add(Weight(prior, C(prior)), Mul(D(4), Sum(Call("range", N()), guarded))), D(0))))
        ]));
    }

    private static Formula AFormula() => Disp(new Formula.Aligned([
        Seq(Named("a"), Colon, Sp, FunctionType(Naturals(), Integers())),
        Seq(Bound("n", Naturals()), Equal(A(N()), Weight(N(), C(N()))))
    ]));

    private static Formula HFormula() => Disp(Seq(HSeries(), Colon, Sp, Series(Integers()), Comma, Sp,
        Equal(HSeries(), Call("mk", LambdaN(Conditional(Equal(N(), D(0)), D(1),
            Conditional(Equal(N(), D(1)), D(1), Mul(Mul(D(4), N()), C(N())))))))));

    private static Formula BFormula() => Disp(Seq(BSeries(), Colon, Sp, Series(Integers()), Comma, Sp,
        Equal(BSeries(), Call("mk", Named("a")))));

    private static Formula RecurrenceFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(2)), Equal(C(N()), Add(A(Subtract(N(), D(1))),
            Mul(D(4), Sum(Call("Ico", D(2), N()), Mul(Mul(K(), C(K())), A(Subtract(N(), K()))))))))));

    private static Formula NormalizationFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(2)), Equal(A(N()), Mul(Parenthesized(Factor(N())), C(N()))))));

    private static Formula IdentityFormula() => Disp(Equation(BSeries(), HSeries(), Integers()));

    private static Formula RationalShapeFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(2)), Equal(Coefficient(N(), Call("mapInt", HSeries())),
            RationalTerm(N(), A(N()))))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("b");
        Formula h = F.Id("h");
        Formula BAt(Formula index) => new Formula.Apply(b, [index]);
        Formula shape = Seq(Bound("n", Naturals()), Implication(AtLeast(N(), D(2)),
            Equal(Coefficient(N(), h), RationalTerm(N(), BAt(N())))));
        Formula conclusion = Seq(Bound("n", Naturals()), Equal(BAt(N()), A(N())));
        return Disp(Seq(Bound("b", FunctionType(Naturals(), Rationals())),
            Bound("h", Series(Rationals())),
            Implication(Equal(BAt(D(0)), D(0)),
            Implication(Equal(BAt(D(1)), D(1)),
            Implication(Equal(Coefficient(D(0), h), D(1)),
            Implication(Equal(Coefficient(D(1), h), D(1)),
            Implication(shape, Implication(Equation(Call("mk", b), h, Rationals()), conclusion))))))));
    }

    private static Formula OddFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(1)), Call("Odd", A(N())))));

    private static Formula Residue(byte index, byte value) => Implication(
        Equal(new Formula.Modulo(N(), D(4)), D(index)),
        Equal(new Formula.Modulo(A(N()), D(8)), D(value)));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(1)), Parenthesized(Conjunction(Residue(1, 1),
            Conjunction(Residue(2, 7), Conjunction(Residue(3, 5), Residue(0, 7))))))));
}
