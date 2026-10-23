using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class KeplerCoulombSphereQESCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/quesne2023keplercoulomb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural m at least two, the Kepler-Coulomb coefficient system has a unique solution on indices zero through m, with positive constants in the conjectured closed forms.",
        H("The Kepler-Coulomb coefficient conjecture"), Blocks(
            Paragraph(Text(
                "The unknown coefficients form a function a from natural numbers to real numbers. "
                    + "Only its values at indices zero through m enter the system and the uniqueness conclusion. "
                    + "All index arithmetic, including subtraction in indices, factorial arguments and exponents, "
                    + "is natural-number arithmetic; subtraction is truncated at zero. "
                    + "Floors denote natural-number division by two. Explicit real type annotations denote casts. "
                    + "Empty sums are zero and empty products are one.")),
            Node("System", "The coefficient equations", SystemFormula(),
                "Equations (4.13)-(4.17) give two initial equations, two indexed families and a final equation selected by the parity of m. The interval sums use Finset.Icc, including both endpoints."),
            Node("series", "A homogeneous polynomial bracket", SeriesFormula(),
                "The leading term is Q to the power 2n. The remaining terms have coefficients d j, with j ranging from one through n, and are homogeneous in Q squared and curvature."),
            Node("delta", "The common denominator", DeltaFormula(),
                "The denominator in (4.19)-(4.24) is the bracket of degree mu with coefficients b."),
            Node("OddForm", "The closed forms for odd m", OddFormula(),
                "Equations (4.19)-(4.21) describe the coefficients when m equals 2mu + 1. The factors in the products are Q squared plus 4(r + 1) squared times curvature. The factorials are natural-number factorials cast to real numbers before division."),
            Node("EvenForm", "The closed forms for even m", EvenFormula(),
                "Equations (4.22)-(4.24) describe the coefficients when m equals 2mu. Here the product factors are Q squared plus (2r + 1) squared times curvature, and the odd-index numerator includes a factor Q squared."),
            Node("ClosedForms", "The two parity cases", ClosedFormula(),
                "The remainder m modulo two chooses the odd or even formulas, with mu equal to the floor of m divided by two."),
            Node("PositiveConstants", "Positivity of the bracket coefficients", PositiveFormula(),
                "The constants b j are positive for one through the floor of m divided by two. For each admissible k, the constants c k j are positive throughout the degree of its bracket. Values of b and c outside these ranges are unrestricted."),
            Node("claim", "Quesne's coefficient conjecture", ClaimFormula(),
                "For each m at least two, the positive constants can be chosen independently of Q and curvature. For every positive Q and curvature the system has a solution, every solution has the displayed closed forms, and any two solutions agree on zero through m. Q is the source's rescaled coupling and kappa is the curvature. Equation (4.18) is omitted because it is a combination of (4.13) and (4.14)."),
            Describe.Lean(
                DescribeId.Create("quesne-coefficients-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Positive constants and the closed-form solution"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Normalize with z = Q squared divided by curvature, dividing each positive even-index coefficient by Q. "
                        + "An explicit polynomial solution satisfies the normalized equations by telescoping identities. "
                        + "The recurrence forces every solution to be proportional to this polynomial solution, "
                        + "and the first equation fixes the proportionality constant. "
                        + "As polynomials in z, the common denominator of (4.19)-(4.24) and, for admissible k, "
                        + "the odd-index brackets have strictly positive coefficients through their degrees; "
                        + "for odd m each bracket is the normalized odd-index numerator, while for even m that "
                        + "numerator has zero constant term and the bracket is that numerator divided by z. "
                        + "Their coefficients give b and c, and evaluation at nonnegative z "
                        + "makes the denominator strictly positive. Rescaling by curvature yields the two families "
                        + "of factorial ratios, products and polynomial brackets."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("quesne-2023-kepler-coulomb-qes-coefficient-conjecture"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("quesne-coefficients-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SystemFormula()
    {
        Formula first = Equal(Subtract(Multiply(Add(RealCast(V("m")), D(1)), A(D(0))), A(D(1))), D(1));
        Formula second = Equal(Subtract(Subtract(Multiply(Multiply(RealCast(V("m")), V("Q")), A(D(0))),
            Multiply(V("Q"), A(D(1)))), SumOver("k", Icc(D(1), Half(V("m"))), A(Twice(V("k"))))), D(0));
        Formula evenRows = ForInterval("k", D(1), Half(Subtract(V("m"), D(1))), Equal(
            Subtract(Subtract(Multiply(Subtract(RealCast(V("m")), Twice(RealCast(V("k")))), A(Twice(V("k")))),
                Multiply(V("Q"), A(Add(Twice(V("k")), D(1))))),
                SumOver("l", Icc(Add(V("k"), D(1)), Half(V("m"))), A(Twice(V("l"))))), D(0)));
        Formula factor = Subtract(Add(RealCast(V("m")), D(1)), Twice(RealCast(V("k"))));
        Formula oddRows = ForInterval("k", D(1), Subtract(Half(V("m")), D(1)), Equal(
            Subtract(Subtract(Multiply(Multiply(Kappa, factor), A(Subtract(Twice(V("k")), D(1)))),
                Multiply(V("Q"), A(Twice(V("k"))))),
                Multiply(Multiply(Kappa, factor), A(Add(Twice(V("k")), D(1))))), D(0)));
        Formula sign = Power(RealCast(new Formula.Negate(D(1))), V("m"));
        Formula oddEnd = Subtract(Subtract(Multiply(Multiply(D(2), Kappa), A(Subtract(V("m"), D(2)))),
            Multiply(V("Q"), A(Subtract(V("m"), D(1))))), Multiply(Multiply(D(2), Kappa), A(V("m"))));
        Formula evenEnd = Subtract(Multiply(Kappa, A(Subtract(V("m"), D(1)))), Multiply(V("Q"), A(V("m"))));
        Formula last = Equal(Add(Multiply(Divide(Subtract(D(1), sign), D(2)), oddEnd),
            Multiply(Divide(Add(D(1), sign), D(2)), evenEnd)), D(0));
        return All("m", Naturals(), Parameters(StateBinder(Equivalence(
            LocalCall("System", V("m"), V("Q"), Kappa, V("a")),
            And(first, And(second, And(evenRows, And(oddRows, last))))))));
    }

    private static Formula SeriesFormula() => All("n", Naturals(), All("d", SequenceType(), Parameters(Equal(
        LocalCall("series", V("n"), V("d"), V("Q"), Kappa),
        Add(Power(V("Q"), Twice(V("n"))), SumOver("j", Icc(D(1), V("n")),
            Multiply(Multiply(At(V("d"), V("j")), Power(Kappa, V("j"))),
                Power(V("Q"), Twice(Subtract(V("n"), V("j")))))))))));

    private static Formula DeltaFormula() => All(Mu, Naturals(), All("b", SequenceType(), Parameters(Equal(
        LocalCall("delta", Mu, V("b"), V("Q"), Kappa),
        LocalCall("series", Mu, V("b"), V("Q"), Kappa)))));

    private static Formula OddFormula()
    {
        Formula zero = Equal(A(D(0)), Divide(Product(Mu, true), Denominator()));
        Formula factorial = FactorialRatio(Add(Twice(Mu), D(1)), Add(Subtract(Twice(Mu), Twice(V("k"))), D(1)));
        Formula even = All("k", Naturals(), Imp(LE(D(1), V("k")), Imp(LE(V("k"), Mu), Equal(
            A(Twice(V("k"))), Divide(Multiply(Multiply(Multiply(factorial, Power(Kappa, V("k"))), V("Q")),
                Product(Subtract(Mu, V("k")), true)), Denominator())))));
        Formula oddFactorial = FactorialRatio(Add(Twice(Mu), D(1)), Subtract(Twice(Mu), Twice(V("k"))));
        Formula odd = All("k", Naturals(), Imp(LE(V("k"), Mu), Equal(A(Add(Twice(V("k")), D(1))),
            Divide(Multiply(Multiply(oddFactorial, Power(Kappa, V("k"))),
                Bracket(Subtract(Mu, V("k")))), Denominator()))));
        return FormBinders(Equivalence(LocalCall("OddForm", Mu, V("Q"), Kappa, V("b"), V("c"), V("a")),
            And(zero, And(even, odd))));
    }

    private static Formula EvenFormula()
    {
        Formula zero = Equal(A(D(0)), Divide(Product(Mu, false), Denominator()));
        Formula factorial = FactorialRatio(Twice(Mu), Subtract(Twice(Mu), Twice(V("k"))));
        Formula even = All("k", Naturals(), Imp(LE(D(1), V("k")), Imp(LE(V("k"), Mu), Equal(
            A(Twice(V("k"))), Divide(Multiply(Multiply(Multiply(factorial, Power(Kappa, V("k"))), V("Q")),
                Product(Subtract(Mu, V("k")), false)), Denominator())))));
        Formula oddFactorial = FactorialRatio(Twice(Mu), Subtract(Subtract(Twice(Mu), Twice(V("k"))), D(1)));
        Formula odd = All("k", Naturals(), Imp(LT(V("k"), Mu), Equal(A(Add(Twice(V("k")), D(1))),
            Divide(Multiply(Multiply(Multiply(oddFactorial, Power(Kappa, V("k"))), Power(V("Q"), D(2))),
                Bracket(Subtract(Subtract(Mu, V("k")), D(1)))), Denominator()))));
        return FormBinders(Equivalence(LocalCall("EvenForm", Mu, V("Q"), Kappa, V("b"), V("c"), V("a")),
            And(zero, And(even, odd))));
    }

    private static Formula ClosedFormula() => All("m", Naturals(), Parameters(Constants(StateBinder(Equivalence(
        LocalCall("ClosedForms", V("m"), V("Q"), Kappa, V("b"), V("c"), V("a")),
        And(Imp(Equal(At(Qualified("Nat", "mod"), V("m"), D(2)), D(1)),
                LocalCall("OddForm", Half(V("m")), V("Q"), Kappa, V("b"), V("c"), V("a"))),
            Imp(Equal(At(Qualified("Nat", "mod"), V("m"), D(2)), D(0)),
                LocalCall("EvenForm", Half(V("m")), V("Q"), Kappa, V("b"), V("c"), V("a")))))))));

    private static Formula PositiveFormula() => All("m", Naturals(), Constants(Equivalence(
        LocalCall("PositiveConstants", V("m"), V("b"), V("c")),
        And(ForInterval("j", D(1), Half(V("m")), LT(D(0), At(V("b"), V("j")))),
            All("k", Naturals(), Imp(LE(V("k"), Half(Subtract(V("m"), D(1)))),
                ForInterval("j", D(1), Subtract(Half(Subtract(V("m"), D(1))), V("k")),
                    LT(D(0), At(V("c"), V("k"), V("j"))))))))));

    private static Formula ClaimFormula()
    {
        Formula system = LocalCall("System", V("m"), V("Q"), Kappa, V("a"));
        Formula other = Seq(V("a"), Apos);
        Formula existence = Some("a", SequenceType(), system);
        Formula forms = StateBinder(Imp(system,
            LocalCall("ClosedForms", V("m"), V("Q"), Kappa, V("b"), V("c"), V("a"))));
        Formula uniqueness = StateBinder(All(other, SequenceType(), Imp(system,
            Imp(LocalCall("System", V("m"), V("Q"), Kappa, other),
                All("i", Naturals(), Imp(LE(V("i"), V("m")),
                    Equal(A(V("i")), At(other, V("i")))))))));
        Formula parameters = Parameters(Imp(LT(D(0), V("Q")), Imp(LT(D(0), Kappa),
            And(existence, And(forms, uniqueness)))));
        return Equivalence(Local("claim"), All("m", Naturals(), Imp(LE(D(2), V("m")),
            Some("b", SequenceType(), Some("c", ArrayType(),
                And(LocalCall("PositiveConstants", V("m"), V("b"), V("c")), parameters))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Analysis",
        "KeplerCoulombSphereQESCoefficients", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula SequenceType() => Parenthesized(new Formula.TypeArrow(Naturals(), Reals()));
    private static Formula ArrayType() => Parenthesized(new Formula.TypeArrow(Naturals(), new Formula.TypeArrow(Naturals(), Reals())));
    private static Formula RealCast(Formula value) => Typed(value, Reals());
    private static Formula Half(Formula value) => Seq(Lfloor, Divide(value, D(2)), Rfloor);
    private static Formula Twice(Formula value) => Multiply(D(2), value);
    private static Formula A(Formula index) => At(V("a"), index);
    private static Formula Icc(Formula lower, Formula upper) => At(Qualified("Finset", "Icc"), lower, upper);
    private static Formula Bracket(Formula degree) => LocalCall("series", degree, At(V("c"), V("k")), V("Q"), Kappa);
    private static Formula Denominator() => LocalCall("delta", Mu, V("b"), V("Q"), Kappa);
    private static Formula FactorialRatio(Formula top, Formula bottom) => Divide(
        RealCast(At(Qualified("Nat", "factorial"), top)), RealCast(At(Qualified("Nat", "factorial"), bottom)));
    private static Formula Product(Formula count, bool odd)
    {
        Formula shifted = odd ? Add(RealCast(V("r")), D(1)) : Add(Twice(RealCast(V("r"))), D(1));
        Formula square = Power(shifted, D(2));
        Formula multiple = odd ? Multiply(D(4), square) : square;
        Formula factor = Add(Power(V("Q"), D(2)), Multiply(multiple, Kappa));
        return Seq(new Formula.Subscript(Prod, Member(Typed(V("r"), Naturals()),
            At(Qualified("Finset", "range"), count))), Sp, Parenthesized(factor));
    }
    private static Formula Parameters(Formula body) => All("Q", Reals(), All(Kappa, Reals(), body));
    private static Formula Constants(Formula body) => All("b", SequenceType(), All("c", ArrayType(), body));
    private static Formula StateBinder(Formula body) => All("a", SequenceType(), body);
    private static Formula FormBinders(Formula body) => All(Mu, Naturals(), Parameters(Constants(StateBinder(body))));
    private static Formula All(string name, Formula type, Formula body) => All(V(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula ForInterval(string name, Formula lower, Formula upper, Formula body) =>
        All(name, Naturals(), Imp(Member(V(name), Icc(lower, upper)), body));
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(Typed(V(name), Naturals()), set)), Sp, Parenthesized(body));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Divide(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
