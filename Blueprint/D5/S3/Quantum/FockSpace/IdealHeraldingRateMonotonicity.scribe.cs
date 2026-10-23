using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class IdealHeraldingRateMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/saied2025photondistillation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ideal heralding rate of the photon distillation protocols strictly decreases from n = 5 and converges to one quarter.",
        H("Monotonicity of the ideal heralding rate"),
        Blocks(
            Node("p-rat", "The rational heralding rate", "pRat", RationalRateFormula(),
                "For n > 2, this is the ideal heralding rate h_n(0) in Equation (III.9) of the source. Theorem III.5 identifies it for n-photon distillation protocols built from an n by n unitary whose first row has every entry equal to 1/sqrt(n). The factorial multiplies the sum. The exponent and the factorial argument use natural subtraction n - 1, whereas n - t in the summand is rational subtraction. The formula defines a rational value for every natural n, with field division equal to zero at a zero denominator.",
                AssessedProvenance.FromLiterature(Source)),
            Node("p", "The real heralding rate", "p", RealRateFormula(),
                "The rational rate is embedded into the real numbers by Rat.cast. This gives the real sequence with the same exact values.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "Strict decrease and the quarter limit", "claim", ClaimFormula(),
                "Conjecture III.7 states that the ideal heralding rate decreases to one quarter for n >= 5. The adjacent inequalities here are strict: p(n + 1) < p(n) for every natural n >= 5. The second clause is convergence along the natural numbers to the real number one quarter, also stated in Theorem III.5(2).",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("ideal-heralding-rate-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The rate strictly decreases to one quarter"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For n >= 1, the finite sum has the exact decomposition p_n = A_n + (-1)^(n - 1) T_n, where A_n = n^2 integral from 0 to 1 of (1 - u) u^(n - 1) exp(n(u - 1)) du and T_n = 2 n! exp(-n) / n^(n - 1). The tail satisfies 0 <= T_n <= 2 n exp(-n).")),
                    Paragraph(Text(
                        "Set r(u) = u exp(u - 1) and K(u) = 2(2u - 1)/(1 + u)^4. A primitive gives A_n = 1/4 + integral from 0 to 1 of K(u) r(u)^n du. Thus A_n - A_(n + 1) is the integral of K(u) r(u)^n (1 - r(u)). Bounding its negative part on [0, 1/2] and its positive part on [1 - 1/n, 1 - 1/(2n)] yields p_n - p_(n + 1) >= 1/(512 n^2) - (4n + 3) exp(-n) for n >= 16. The right side is positive, since 512 n^2 (4n + 3) < exp(n) on this range.")),
                    Paragraph(Text(
                        "Exact rational evaluation gives p_n - p_(n + 1) > 0 for every n from 5 through 15, completing strict decrease for n >= 5. The kernel representation gives |A_n - 1/4| <= 2/(n + 1), and the tail bound gives |p_n - 1/4| <= 3/n for n >= 16. Squeezing this error to zero proves convergence to one quarter."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("saied-marshall-anand-rieffel-2025-heralding-rate-monotonicity"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("ideal-heralding-rate-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "FockSpace", "IdealHeraldingRateMonotonicity", name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Type(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula SumOver(string variable, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp,
        Parenthesized(body));

    private static Formula RationalRateFormula()
    {
        Formula n = F.Id("n"), t = F.Id("t"), rationals = Type("Q");
        Formula predecessor = Typed(Subtract(n, D(1)), Type("N"));
        Formula power = new Formula.Power(
            Parenthesized(new Formula.Fraction(Typed(new Formula.Negate(D(1)), rationals),
                Typed(n, rationals))), predecessor);
        Formula factorial = Typed(At(Qualified("Nat", "factorial"), predecessor), rationals);
        Formula summand = new Formula.Fraction(
            Multiply(Parenthesized(Subtract(Typed(n, rationals), Typed(t, rationals))),
                new Formula.Power(Parenthesized(new Formula.Negate(Typed(n, rationals))), t)),
            Typed(At(Qualified("Nat", "factorial"), t), rationals));
        return All("n", Type("N"), Equal(LocalCall("pRat", n),
            Multiply(Multiply(power, factorial), SumOver("t", At(Qualified("Finset", "range"), n), summand))));
    }

    private static Formula RealRateFormula() => All("n", Type("N"),
        Equal(LocalCall("p", F.Id("n")),
            Typed(At(Qualified("Rat", "cast"), LocalCall("pRat", F.Id("n"))), Type("R"))));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula decrease = All("n", Type("N"), Implies(AtMost(D(5), n),
            LessThan(LocalCall("p", Add(n, D(1))), LocalCall("p", n))));
        Formula limit = At(Qualified("Filter", "Tendsto"), Local("p"),
            Qualified("Filter", "atTop"),
            At(Qualified("nhds"), Typed(new Formula.Fraction(D(1), D(4)), Type("R"))));
        return Equivalent(Local("claim"), And(decrease, limit));
    }
}
