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
                "Let S be a finite set with real frequencies g and nonnegative weights w. "
                + "Write A(t) for the weighted mean of sin(g(j)t) at one common real time t. "
                + "For a nonempty time set T, D(T) is one minus the supremum of A(t) over T. "
                + "Taking T to be all real times gives the unrestricted deficit. Lean uses zero "
                + "for a quotient with zero denominator.")),
            Result("omissionFraction_isLeast", "Minimum omitted weight",
                Disp(Call("IsLeast", new Formula.Subscript(F.Id("C"), F.Id("h")), P(F.Id("h")))),
                "At integer length h, the set Cₕ contains the omitted weight fractions for subsets "
                + "U of S with the following property. Every integer relation supported on U, "
                + "with coefficient ℓ¹ norm at most h, has coefficient sum divisible by four. "
                + "The empty subset is always admissible. The set of candidate fractions is "
                + "finite, so its infimum Pₕ is attained."),
            Result("simultaneous_bound", "Simultaneous bound at a common time",
                Disp(All("t", Reals, All("N", Naturals,
                    Le(Partial(F.Id("N")), Sub(D(1), Call("A", F.Id("t"))))))),
                "For each h from 1 through N, retain coordinates whose loss 1 − sin(g(j)t) "
                + "is strictly below 1/h². The large-loss inequality for a short relation "
                + "makes this retained set admissible at h. The weight omitted therefore "
                + "bounds Pₕ times the total weight. For each coordinate the threshold levels "
                + "it meets or exceeds form a final segment of the finite sum. Its charge "
                + "telescopes and is bounded by that coordinate's loss. Summing these charges "
                + "proves the inequality at the original time t, including N = 0."),
            Result("aggregate_bounds", "Series and single-length bounds", Aggregate(),
                "The terms are nonnegative and the finite sums are bounded by D(T), so the "
                + "series converges to L. Since Pₕ is nondecreasing, the series tail from h "
                + "is at least Pₕ times the telescoping sum of the coefficients from h, "
                + "which equals 1/h²."),
            Result("strict_three_frequency_example", "Strict improvement with three frequencies",
                Example(),
                "Use frequencies (0, 1, 2) with weights (1/2, 1/4, 1/4). The relation "
                + "(1, 0, 0) forces deletion of the zero frequency at every positive length. "
                + "After that deletion, the shortest nonzero relation on the remaining pair "
                + "has length three. The relation (0, 2, −1) forces deletion of one more "
                + "frequency at length three and above, and retaining frequency 1 alone is "
                + "admissible for all lengths. The single-length supremum is attained at "
                + "length one. The fifth partial sum exceeds it by 1/144."))));

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

    private static Formula Partial(Formula upper)
    {
        var h = F.Id("h");
        var next = new Formula.Binary(h, FormulaBinaryOperator.Add, D(1));
        var coefficient = Sub(Frac(D(1), new Formula.Power(h, D(2))),
            Frac(D(1), new Formula.Power(Seq(Open, next, Close), D(2))));
        var term = new Formula.Binary(Seq(Open, coefficient, Close), FormulaBinaryOperator.Multiply, P(h));
        return Seq(new Formula.Subscript(Sum, Seq(Le(D(1), h), Sp, Leq, Sp, upper)), Sp, term);
    }

    private static Formula Aggregate()
    {
        var limit = F.Id("L");
        var sequence = Seq(Open, F.Id("N"), Sp, Mapsto, Sp, Partial(F.Id("N")), Close);
        var deficit = Call("D", F.Id("T"));
        return Disp(And(All("N", Naturals, Le(Partial(F.Id("N")), deficit)),
            And(Call("Tendsto", sequence, Infty, limit),
                And(Le(SingleScaleSupremum(), limit), Le(limit, deficit)))));
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
        var high = All("h", Naturals, new Formula.Logic(Le(D(3), h), FormulaLogicOperator.Implies,
            Equal(P(h), Frac(D(3), D(4)))));
        return Disp(And(And(Equal(P(D(1)), half), And(Equal(P(D(2)), half), high)),
            And(Equal(SingleScaleSupremum(), half),
                And(Equal(Partial(D(5)), Frac(D(7, 3), D(1, 4, 4))),
                    Lt(SingleScaleSupremum(), Partial(D(5)))))));
    }
}
