using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class PhaseObstructionLengthsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short integer relation obstructions give a simultaneous bound on weighted sine loss.",
        H("Phase Obstructions Across Relation Lengths"),
        Blocks(
            Paragraph(Text(
                "Let S be a finite set with real frequencies g and real weights w. "
                + "Write A(t) for the weighted mean of sin(g(j)t) at one common real time t. "
                + "For any set T of real times, D(T) is one minus the supremum of A(t) over T, "
                + "with D(∅) = 1. Taking T to be all real times gives the unrestricted deficit. "
                + "Lean uses zero for a quotient with zero denominator.")),
            Result("omissionFraction_isLeast", "Minimum omitted weight",
                Disp(Call("IsLeast", new Formula.Subscript(F.Id("C"), F.Id("h")), P(F.Id("h")))),
                "At integer length h, the set Cₕ contains the omitted weight fractions for subsets "
                + "U of S with the following property. Every integer relation supported on U, "
                + "with coefficient ℓ¹ norm at most h, has coefficient sum divisible by four. "
                + "The empty subset is always admissible. The set of candidate fractions is "
                + "finite, so its infimum Pₕ is attained for arbitrary real weights."),
            Paragraph(Text(
                "For the phase bounds assume w(j) ≥ 0 on S. Write Sₙ for the sum of "
                + "(h⁻² − (h+1)⁻²) Pₕ over 1 ≤ h ≤ n and L for the series sum.")),
            Result("simultaneous_bound", "Simultaneous bound at a common time",
                Disp(All("t", Reals, All("N", Naturals,
                    Le(WithResidual(F.Id("N")), Sub(D(1), Call("A", F.Id("t"))))))),
                "For each h from 1 through N + 1, retain coordinates whose loss 1 − sin(g(j)t) "
                + "is strictly below 1/h². A short incompatible relation forces a loss at least "
                + "1/h² at one of its coordinates, so the retained set is admissible at h. "
                + "Its omitted weight bounds Pₕ times the total weight. Give the final threshold "
                + "the full coefficient 1/(N+1)². For each coordinate, the coefficients of the "
                + "thresholds it meets or exceeds telescope to a value bounded by its loss."),
            Result("aggregate_bounds", "Series, single-length bounds and remainder", Aggregate(),
                "The common-time inequality gives the finite bound by taking the supremum of A(t) "
                + "over a nonempty T. For the empty time set, Pₕ ≤ 1 bounds the finite sum and its "
                + "residual by the corresponding telescoping sum, which equals D(∅) = 1. "
                + "The nonnegative series terms are bounded by the summable coefficients. In "
                + "the tail after N, every Pₕ is between Pₙ₊₁ and 1, and the coefficient sum is "
                + "1/(N+1)². Taking N = h − 1 and using Sₙ ≥ 0 gives single-length dominance."),
            Result("strict_three_frequency_example", "Strict improvement with three frequencies",
                Example(),
                "Use frequencies (0, 1, 2) with weights (1/2, 1/4, 1/4). The relation "
                + "(1, 0, 0) forces deletion of the zero frequency at every positive length. "
                + "After that deletion, the shortest nonzero relation on the remaining pair "
                + "has length three. The relation (0, 2, −1) forces deletion of one more "
                + "frequency at length three and above, and retaining frequency 1 alone is "
                + "admissible for all lengths. The single-length supremum is attained at "
                + "length one. Starting after the second term, the omitted fraction is constant, "
                + "so telescoping gives the partial sums and the series value. The partial sums "
                + "are nondecreasing and the fourth is 112/225. The fifth is the first to "
                + "exceed the single-length supremum."),
            Paragraph(Text(
                "In particular, for a nonempty finite frequency set, positive weights and "
                + "all real times, dropping the nonnegative residual gives the original finite "
                + "inequality. The series comparison and the fifth partial sum give the original "
                + "infinite and strict finite comparisons. An application to actual zeta cutoffs "
                + "requires independent relation bounds for the ordinates.")))));

    private static DocumentBlock Result(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/PhaseObstructionLengths." + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula P(Formula h) => new Formula.Subscript(F.Id("P"), h);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Partial(Formula n) => new Formula.Subscript(F.Id("S"), n);
    private static Formula Increment(Formula n) => Add(n, D(1));
    private static Formula NextSquare(Formula n) =>
        new Formula.Power(Seq(Open, Increment(n), Close), D(2));
    private static Formula Residual(Formula n) => Frac(P(Increment(n)), NextSquare(n));
    private static Formula WithResidual(Formula n) => Add(Partial(n), Residual(n));

    private static Formula Aggregate()
    {
        var n = F.Id("N");
        var index = F.Id("n");
        var limit = F.Id("L");
        var deficit = Call("D", F.Id("T"));
        var secondSuccessor = new Formula.Power(Seq(Open, Add(index, D(2)), Close), D(2));
        var coefficient = Sub(Frac(D(1), NextSquare(index)), Frac(D(1), secondSuccessor));
        var seriesTerm = Mul(Seq(Open, coefficient, Close), P(Increment(index)));
        var sequence = Seq(Open, index, Sp, Mapsto, Sp, seriesTerm, Close);
        var remainder = Sub(limit, Partial(n));
        return Disp(And(All("N", Naturals, Le(WithResidual(n), deficit)),
            And(Call("HasSum", sequence, limit),
                And(Le(SingleScaleSupremum(), limit), And(Le(limit, deficit),
                    All("N", Naturals, And(Le(Residual(n), remainder),
                        Le(remainder, Frac(D(1), NextSquare(n))))))))));
    }

    private static Formula SingleScaleSupremum()
    {
        var h = F.Id("h");
        return Seq(new Formula.Subscript(Seq(Operatorname, Grp(F.Id("sup"))), Le(D(1), h)),
            Sp, Frac(P(h), new Formula.Power(h, D(2))));
    }

    private static Formula Example()
    {
        var h = F.Id("h");
        var half = Frac(D(1), D(2));
        var n = F.Id("N");
        var high = All("h", Naturals, Imp(Le(D(3), h), Equal(P(h), Frac(D(3), D(4)))));
        var sum = Frac(D(1, 9), D(3, 6));
        var formula = All("N", Naturals, Imp(Le(D(2), n),
            Equal(Partial(n), Sub(sum, Frac(D(3), Mul(D(4), NextSquare(n)))))));
        var improving = Seq(OpenBrace, n, Colon, Sp, Naturals, Sp, Mid, Sp,
            Lt(SingleScaleSupremum(), Partial(n)), CloseBrace);
        return Disp(And(And(Equal(P(D(1)), half), And(Equal(P(D(2)), half), high)),
            And(Equal(SingleScaleSupremum(), half),
                And(Equal(Partial(D(5)), Frac(D(7, 3), D(1, 4, 4))),
                    And(Lt(SingleScaleSupremum(), Partial(D(5))),
                        And(Equal(F.Id("L"), sum), And(formula, Call("IsLeast", improving, D(5)))))))));
    }
}
