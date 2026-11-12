using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaSquareExponentIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/hanna2021a350410family");
    private const string IntegralityQuote = "OEIS A350410, A350411 and A350412, COMMENTS (web entries, no page numbers): \"This sequence is conjectured to consist entirely of integers.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Existence, uniqueness and integer coefficients for Hanna's three square-exponent factorial series.",
        H("Hanna's Square-Exponent Factorial Integrality"), Blocks(
            Node("squarePowerSum", "The finite square-power sum",
                All("M", N(), All("B", PS(), Eqn(Call("squarePowerSum", V("M"), V("B")),
                    Qualified("Finset", "sum", Qualified("Finset", "range", Add(V("M"), D(1))),
                        Lam("m", N(), Qualified("HSMul", "hSMul", new Formula.Fraction(D(1), Cast(Qualified("Nat", "factorial", V("m")), Q())),
                            Pow(V("B"), Mul(V("m"), V("m"))))))))),
                "The sum runs from zero through M, inclusive. Scalar division is rational and each factorial is positive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("normalized", "The first two coefficients",
                All("B", PS(), Iffn(Call("normalized", V("B")), Normalized(V("B")))) ,
                "The first two source examples start with -1+x; the coefficients are ordinary formal power-series coefficients.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("vanishingEquation", "The degree-dependent equations",
                All("cutoff", Seq(N(), Sp, To, Sp, N()), All("B", PS(),
                    Iffn(Call("vanishingEquation", V("cutoff"), V("B")),
                        And(Call("normalized", V("B")), All("n", N(), Imp(Le(D(2), V("n")),
                            Eqn(Coeff(V("n"), Call("squarePowerSum", Apply(V("cutoff"), V("n")), V("B"))), D(0)))))))),
                "The normalized rational series satisfies the coefficient equation in every degree at least two, with the upper endpoint chosen by cutoff.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isSourceA350410", "The first source series",
                All("A", PS(), Iffn(Call("isSourceA350410", V("A")), Call("vanishingEquation", Lam("n", N(), V("n")), V("A")))),
                "OEIS A350410, NAME (revision 5, no page number): \"G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n} A(x)^(m^2) / m!, for n > 1.\" The EXAMPLE starts -1+x, fixing the two initial coefficients.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isSourceA350411", "The second source series",
                All("A", PS(), Iffn(Call("isSourceA350411", V("A")), Call("vanishingEquation", Lam("n", N(), Add(V("n"), D(1))), V("A")))),
                "OEIS A350411, NAME (revision 5, no page number): \"G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n+1} A(x)^(m^2) / m!, for n > 1.\" The EXAMPLE starts -1+x, fixing the two initial coefficients.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isSourceA350412", "The third source series",
                All("A", PS(), Iffn(Call("isSourceA350412", V("A")),
                    And(Eqn(Qualified("PowerSeries", "constantCoeff", V("A")), D(0)),
                        And(Eqn(Coeff(D(1), V("A")), D(1)), All("n", N(), Imp(Le(D(2), V("n")),
                            Eqn(Coeff(V("n"), Call("squarePowerSum", Mul(D(2), V("n")), Sub(V("A"), D(1)))), D(0)))))))),
                "OEIS A350412, NAME (revision 9, no page number): \"G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..2*n} (A(x) - 1)^(m^2) / m!, for n > 1, with A(0) = 0.\" The EXAMPLE starts x, so the degree-one coefficient is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The three integrality assertions", Iffn(Call("claim"), ClaimBody()),
                IntegralityQuote + " For each of the three preceding source equations, there is exactly one rational series with the stated initial coefficients, and every coefficient of every such series is an integer. All degrees, including zero, occur in the integer-coefficient assertions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All three series exist uniquely and have integer coefficients", ClaimBody(),
                "The factorial slope is nonzero. Differentiation makes the exceptional last numerator divisible by the cutoff; the remaining factorials already divide the clearing factorial. The resulting integer coefficient operator has a fixed point by prefix contraction. Translation by one gives the third series.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-hanna350410"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannasquareexponentintegrality-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name))) : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Apply(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) => Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula a) => Qualified("PowerSeries", "coeff", n, a);
    private static Formula Normalized(Formula b) => And(Eqn(Qualified("PowerSeries", "constantCoeff", b), new Formula.Negate(D(1))), Eqn(Coeff(D(1), b), D(1)));
    private static Formula Integral(Formula a) => All("n", N(), Ex("z", Z(), Eqn(Coeff(V("n"), a), Cast(V("z"), Q()))));
    private static Formula Existence(string predicate) => Ex("A", PS(), And(Call(predicate, V("A")),
        All("Ap", PS(), Imp(Call(predicate, V("Ap")), Eqn(V("Ap"), V("A"))))));
    private static Formula Integrality(string predicate) => All("A", PS(), Imp(Call(predicate, V("A")), Integral(V("A"))));
    private static Formula ClaimBody() => And(Existence("isSourceA350410"), And(Integrality("isSourceA350410"),
        And(Existence("isSourceA350411"), And(Integrality("isSourceA350411"), And(Existence("isSourceA350412"), Integrality("isSourceA350412"))))));
}
