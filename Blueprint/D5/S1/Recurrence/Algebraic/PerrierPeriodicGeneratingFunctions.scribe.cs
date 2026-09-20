using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class PerrierPeriodicGeneratingFunctionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/perrier2026mcf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perrier's period-one series satisfy both numerator identities over commutative rings.",
        H("Perrier's Period-One Generating Functions"),
        Blocks(
            Paragraph(Text(
                "Let K be any commutative ring and d any natural number, including zero. Set k=d+1. "
                + "The source uses coordinates 1,...,k; here they are Fin(d+1). "
                + "Thus r(n,j) denotes the source coordinate j+1 at time n-1, "
                + "and m(j), a(j) denote its parameters with index j+1. "
                + "The maps succ and castSucc send j in Fin(d) to coordinates j+1 "
                + "and j in Fin(d+1); last(d) is coordinate d. "
                + "All series lie in K[[X]], C embeds a ring element as a constant series, "
                + "and val(j) is the natural value of a finite index. "
                + "Subtraction in an exponent is natural subtraction, truncated at zero. "
                + "Every finite sum below ranges over all j in Fin(d), so it is empty at d=0.")),
            Node("Recurrence", "The period-one recurrence", RecurrenceFormula(),
                "Perrier, printed p. 14: \"The same method extends to higher dimensions.\" "
                + "The next paragraph states: \"Assume period 1, so mⱼ,ᵢ = mⱼ for "
                + "1 ≤ j ≤ k − 1 and i ≥ 0.\" The initial values are "
                + "r₁⁽⁻¹⁾ = 1, r₂⁽⁻¹⁾ = a₁, ..., rₖ⁽⁻¹⁾ = aₖ₋₁. "
                + "On printed p. 15 the recurrences are r₁⁽ⁿ⁺¹⁾ = rₖ⁽ⁿ⁾ and "
                + "rⱼ₊₁⁽ⁿ⁺¹⁾ = rⱼ⁽ⁿ⁾ + mⱼrₖ⁽ⁿ⁾, 1 ≤ j ≤ k − 1. "
                + "The four conjuncts above retain these initial values and both equations "
                + "as a predicate on an arbitrary sequence. For every m and a, the "
                + "initial vector and the next-vector rule recursively determine one "
                + "and only one sequence, so the predicate has a solution.", DescribeRole.Definition),
            Node("R", "The shifted generating function", RFormula(),
                "Perrier, printed p. 8: \"To retain the stated initial values, define "
                + "the shifted generating functions\" R₁(t) = ∑ₙ≥₀ r₁⁽ⁿ⁻¹⁾tⁿ, "
                + "R₂(t) = ∑ₙ≥₀ r₂⁽ⁿ⁻¹⁾tⁿ. Printed p. 12 states: "
                + "\"Define the shifted generating functions\" Rᵢ(t) = ∑ₙ≥₀ rᵢ⁽ⁿ⁻¹⁾tⁿ, "
                + "i = 1, 2, 3. The coefficient function n ↦ r(n,j) implements that "
                + "shift literally. Section 5 does not repeat this definition for general k; "
                + "its opening sentence, \"The same method extends to higher dimensions.\", "
                + "is read as retaining the preceding shifted convention.", DescribeRole.Definition),
            Node("D", "The common denominator", DFormula(),
                "This is the denominator printed on p. 15, with m₁ attached to t^(k-1) "
                + "and mₖ₋₁ attached to t. The sum writes the same terms in the opposite "
                + "order. Each exponent d-val(j) is positive, so D(m) has constant "
                + "coefficient one and is invertible as a formal power series.", DescribeRole.Definition),
            Node("P", "The first-coordinate numerator", PFormula(),
                "This is the numerator of R₁ on printed p. 15. The source difference "
                + "aⱼ-mⱼ becomes C(a(j)-m(j)) at exponent d-val(j), "
                + "and the remaining constant term is one.", DescribeRole.Definition),
            Node("Q", "The last-coordinate numerator", QFormula(),
                "This is the numerator of Rₖ on printed p. 15. Its leading term "
                + "is X^d, and parameter a(j) has exponent d-1-val(j). "
                + "For d=0 the finite sum is empty and X^d is one.", DescribeRole.Definition),
            Node("result", "The two rational generating functions", ResultFormula(),
                "Perrier, Section 5, printed p. 15: \"We conjecture that solving these "
                + "recurrences yields\" the displayed formulas for R₁(t) and Rₖ(t). "
                + "The formal conclusion is R(r,0)D(m)=P(m,a) and R(r,last(d))D(m)=Q(a). "
                + "Both identities hold for every sequence satisfying Recurrence(m,a,r), "
                + "over every commutative ring and every d, including zero. "
                + "Section 5 names no coefficient domain. Its ambient construction is integral; "
                + "the commutative-ring statement specializes directly to the integers. "
                + "Multiplying the successor-coordinate equations by X^(d-1-val(j)) "
                + "and summing cancels all intermediate coordinates. This gives "
                + "R(r,last(d))D(m)=Q(a); the first-coordinate equation gives "
                + "R(r,0)D(m)=P(m,a). The constant coefficient one makes D(m) a unit, "
                + "so these products are equivalent to the printed quotients. "
                + "The subsequent sentence about equation (7) is a separate conjecture.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "perrier-multidimensional-continued-fraction-generating-functions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("perrier-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            name == "result"
                ? Blocks(Paragraph(Text(prose)),
                    Paragraph(Text("The two formulas quoted from printed p. 15, in the source notation, are:")),
                    new DocumentBlock.DisplayFormula(PrintedIdentities()))
                : Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula K => F.Id("K");
    private static Formula Dim => F.Id("d");
    private static Formula X => F.Id("X");
    private static Formula J => F.Id("j");
    private static Formula N => F.Id("n");
    private static Formula M => F.Id("m");
    private static Formula A => F.Id("a");
    private static Formula Rr => F.Id("r");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula EqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula AndF(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula FinD => Call("Fin", Dim);
    private static Formula FinNext => Call("Fin", Add(Dim, D(1)));
    private static Formula Parameters => Arrow(FinD, K);
    private static Formula Sequences => Arrow(Naturals, Arrow(FinNext, K));
    private static Formula Context(Formula body) => Seq(
        Bound("K", Seq(Operatorname, Grp(F.Id("Type")))), Call("CommRing", K), Sp, Implies, Sp,
        Bound("d", Naturals), body);
    private static Formula SumFin(Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(J, Sp, InMacro, Sp, FinD)), Sp, Parenthesized(body));
    private static Formula Exponent => Sub(Dim, Call("val", J));
    private static Formula LowerExponent => Sub(Sub(Dim, D(1)), Call("val", J));

    private static Formula RecurrenceFormula()
    {
        var initial = EqF(Call("r", D(0), D(0)), D(1));
        var others = Seq(Bound("j", FinD), EqF(Call("r", D(0), Call("succ", J)), Call("a", J)));
        var firstStep = Seq(Bound("n", Naturals), EqF(
            Call("r", Add(N, D(1)), D(0)), Call("r", N, Call("last", Dim))));
        var otherSteps = Seq(Bound("n", Naturals), Bound("j", FinD), EqF(
            Call("r", Add(N, D(1)), Call("succ", J)),
            Add(Call("r", N, Call("castSucc", J)), Mul(Call("m", J), Call("r", N, Call("last", Dim))))));
        return Disp(Context(Seq(Bound("m", Parameters), Bound("a", Parameters), Bound("r", Sequences),
            Call("Recurrence", M, A, Rr), Sp, Iff, Sp,
            AndF(initial, AndF(others, AndF(firstStep, otherSteps))))));
    }

    private static Formula RFormula() => Disp(Context(Seq(Bound("r", Sequences), Bound("j", FinNext),
        EqF(Call("R", Rr, J), Call("mk", Seq(N, Sp, Mapsto, Sp, Call("r", N, J)))))));
    private static Formula DFormula() => Disp(Context(Seq(Bound("m", Parameters),
        EqF(Call("D", M), Sub(Sub(D(1), SumFin(Mul(Call("C", Call("m", J)), Pow(X, Exponent)))),
            Pow(X, Add(Dim, D(1))))))));
    private static Formula PFormula() => Disp(Context(Seq(Bound("m", Parameters), Bound("a", Parameters),
        EqF(Call("P", M, A), Add(D(1), SumFin(Mul(Call("C", Sub(Call("a", J), Call("m", J))),
            Pow(X, Exponent))))))));
    private static Formula QFormula() => Disp(Context(Seq(Bound("a", Parameters),
        EqF(Call("Q", A), Add(Pow(X, Dim), SumFin(Mul(Call("C", Call("a", J)),
            Pow(X, LowerExponent))))))));
    private static Formula ResultFormula() => Disp(Context(Seq(
        Bound("m", Parameters), Bound("a", Parameters), Bound("r", Sequences),
        Call("Recurrence", M, A, Rr), Sp, Implies, Sp,
        AndF(EqF(Mul(Call("R", Rr, D(0)), Call("D", M)), Call("P", M, A)),
            EqF(Mul(Call("R", Rr, Call("last", Dim)), Call("D", M)), Call("Q", A))))));

    private static Formula PrintedIdentities()
    {
        Formula k = F.Id("k"), t = F.Id("t"), dots = Seq(Cdot, Cdot, Cdot);
        Formula At(string name, Formula index) => new Formula.Subscript(F.Id(name), index);
        Formula Term(string name, Formula index, Formula exponent) => Mul(At(name, index), Pow(t, exponent));
        Formula Difference(Formula index, Formula exponent) =>
            Mul(Parenthesized(Sub(At("a", index), At("m", index))), Pow(t, exponent));
        var km1 = Sub(k, D(1));
        var km2 = Sub(k, D(2));
        var denominator = Sub(Sub(Sub(Sub(Sub(D(1), Mul(At("m", km1), t)),
            Term("m", km2, D(2))), dots), Term("m", D(1), km1)), Pow(t, k));
        var first = Add(Add(Add(Add(Difference(D(1), km1), Difference(D(2), km2)), dots),
            Mul(Parenthesized(Sub(At("a", km1), At("m", km1))), t)), D(1));
        var last = Add(Add(Add(Add(Pow(t, km1), Term("a", D(1), km2)), dots),
            Mul(At("a", km2), t)), At("a", km1));
        return new Formula.Aligned([
            EqF(new Formula.Apply(At("R", D(1)), [t]), new Formula.Fraction(first, denominator)),
            EqF(new Formula.Apply(At("R", k), [t]), new Formula.Fraction(last, denominator)),
        ]);
    }
}
