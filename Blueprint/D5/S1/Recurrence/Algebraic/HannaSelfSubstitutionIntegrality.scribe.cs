using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaSelfSubstitutionIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.";
    private const string SourceSentence = "Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies: G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/hanna2009a163921a157675");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral exponential inputs give integral Hanna self-substitution fixed points.",
        H("Hanna's Self-Substitution Integrality"),
        Blocks(
            Paragraph(Text("All series are ordinary formal power series over the rationals. "
                + "IntegralSeries means that each coefficient is the image of an integer. "
                + "The index zero of L is unused. In logSum, N-n is subtraction in the natural "
                + "numbers; division is in the rationals after casting n. The finite coefficient "
                + "sum defines the infinite formal sum without an analytic convergence condition.")),
            Node("logSum", "The coefficientwise logarithmic sum", LogSumFormula(),
                "OEIS A163921, comment (unpaginated): \"" + SourceSentence + "\" "
                    + "For a series-valued family f, the degree-N coefficient of Sum_{n>=1} "
                    + "f(n)*x^n/n is the sum of coeff(N-n,f(n))/n over 1<=n<=N.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SolvesHanna", "The self-substitution equation", SolvesFormula(),
                "OEIS A163921, comment (unpaginated): \"" + SourceSentence + "\" "
                    + "PowerSeries.rescale (L n) G is G(L(n)*x); the nth power is multiplied "
                    + "by x^n through logSum. PowerSeries.subst substitutes the zero-constant "
                    + "logarithmic sum into PowerSeries.exp.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's integrality conjecture",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A163921, comment (unpaginated): \"" + SourceSentence + "\" "
                    + "L ranges over rational sequences. The conclusion asserts that a solution "
                    + "exists and that every solution has integer coefficients. Integral input "
                    + "forces all positive-index values of L to be integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integral self-substitution fixed points", Disp(ClaimBody()),
                "For every rational sequence L with integral exponential input, the positive-index "
                    + "values L(n) have integer representatives c(n). The integer Euler ledger "
                    + "of the input gives p dividing c(p*m)-c(m) for every prime p and positive m. "
                    + "Frobenius and power lifting show that "
                    + "the exponential self-substitution operator preserves integer coefficients "
                    + "by the sufficient Dieudonne-Dwork criterion. Its logarithmic sum has "
                    + "constant coefficient zero, so every output has constant coefficient one. "
                    + "The operator raises coefficient agreement by one degree. "
                    + "PowerSeriesNormalizedContraction.exists_unique_fixed supplies a unique "
                    + "rational solution. Starting from 1, each iterate has integer coefficients. "
                    + "For every natural degree N, every solution agrees through degree N with "
                    + "the Nth iterate, so its degree-N coefficient is an integer. Thus a solution "
                    + "exists and every solution is integral in every degree. These are formal "
                    + "power-series statements without an analytic convergence hypothesis or "
                    + "a finite degree bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hannasubst"), ResolutionKind.Proved)),
            Node("geometric_input", "Geometric exponential inputs",
                Disp(All("a", Int(), Integral(Exponential(Call("logSum",
                    Lambda("n", Nat(), App(Q("PowerSeries", "C"),
                        Pow(Cast(V("a"), Rat()), V("n"))))))))),
                "For every integer a the exponential of Sum_{n>=1} a^n*x^n/n equals "
                    + "(1-a*X) inverse and has integer coefficients. The specialization a=2 "
                    + "supplies the input for the A157675 equation through "
                    + "HannaSelfSubstitutionIntegralityA157675.result. The identity and "
                    + "integrality hold at every natural degree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hanna-self-substitution-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula LogSumFormula()
    {
        var numerator = App(Q("PowerSeries", "coeff"),
            new Formula.Binary(V("N"), FormulaBinaryOperator.Subtract, V("n")),
            App(V("f"), V("n")));
        var summand = new Formula.Fraction(numerator, Cast(V("n"), Rat()));
        var sum = App(Q("Finset", "sum"), App(Q("Finset", "Icc"), D(1), V("N")),
            Lambda("n", Nat(), summand));
        return Disp(All("f", Seq(Nat(), Sp, To, Sp, PS()),
            Equal(Call("logSum", V("f")),
                App(Q("PowerSeries", "mk"), Lambda("N", Nat(), sum)))));
    }

    private static Formula SolvesFormula() => Disp(All("L", Seq(Nat(), Sp, To, Sp, Rat()),
        All("G", PS(), Equal(Call("SolvesHanna", V("L"), V("G")),
            Parenthesized(Equal(V("G"), Exponential(Call("logSum", Lambda("n", Nat(),
                Pow(App(Q("PowerSeries", "rescale"), App(V("L"), V("n")), V("G")),
                    V("n")))))))))));

    private static Formula ClaimBody() => All("L", Seq(Nat(), Sp, To, Sp, Rat()),
        Imp(Integral(Exponential(Call("logSum", Lambda("n", Nat(),
                App(Q("PowerSeries", "C"), App(V("L"), V("n"))))))),
            new Formula.Logic(
                Parenthesized(Ex("G", PS(), Call("SolvesHanna", V("L"), V("G")))),
                FormulaLogicOperator.And,
                Parenthesized(All("G", PS(), Imp(Call("SolvesHanna", V("L"), V("G")), Integral(V("G"))))))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        App(Seq(Operatorname, Grp(V(name))), arguments);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Rat());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Integral(Formula series) =>
        App(Q("HannaLogarithmicPowerClosure", "IntegralSeries"), series);
    private static Formula Exponential(Formula input) =>
        App(Q("PowerSeries", "subst"), input, App(Q("PowerSeries", "exp"), Rat()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
}
