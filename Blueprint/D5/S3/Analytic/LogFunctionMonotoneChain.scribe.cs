using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LogFunctionMonotoneChainDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/LogFunctionMonotoneChain";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/AnalyticClosure/maweigert2025logfunctions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed derivative regions of polynomial log-functions form a descending chain with completely monotone intersection.",
        H("A descending chain for polynomial log-functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-function"),
                DeclarationHandle.Create(Module + ".logFunction"),
                H("A polynomial in the logarithm divided by its argument"),
                StatementSource.FromAuthor(Disp(LogFunctionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real polynomial p, the associated function is p(log x)/x. "
                    + "This is the univariate case of the class in Intro.tex, lines 20–23. "
                    + "The formula defines a function on all real arguments, while every "
                    + "derivative sign condition below concerns only x > 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("derivative-region"),
                DeclarationHandle.Create(Module + ".derivativeRegion"),
                H("The region determined by one signed derivative"),
                StatementSource.FromAuthor(Disp(DerivativeRegionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The region consists of real polynomials of natural degree at most n "
                    + "whose associated log-function has nonnegative signed kth derivative "
                    + "at every positive argument. The natural degree of the zero polynomial "
                    + "is zero. These are the polynomial parameters of the function regions "
                    + "in infiniteOrderDeriv.tex, lines 154–159. The positive domain is the "
                    + "one specified in Intro.tex, line 22, and in the preceding example, "
                    + "infiniteOrderDeriv.tex, line 150."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completely-monotone"),
                DeclarationHandle.Create(Module + ".completelyMonotone"),
                H("All signed derivative inequalities on the positive half-line"),
                StatementSource.FromAuthor(Disp(CompletelyMonotoneDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every derivative order, including order zero, must have its alternating "
                    + "sign nonnegative at every positive point. Order zero requires the "
                    + "function itself to be nonnegative. Intro.tex, lines 1–4, states "
                    + "complete monotonicity for smooth functions. This predicate records "
                    + "the derivative sign conditions alone, without a separate smoothness "
                    + "hypothesis; below it is applied to polynomial log-functions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Nesting and the intersection for every degree bound"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural degree bound n, the region of order k + 1 is "
                    + "contained in the region of order k whenever k is at least one. "
                    + "For each polynomial of natural degree at most n, membership in "
                    + "all regions of positive order is equivalent to complete monotonicity "
                    + "of its log-function. This expresses the nesting and intersection "
                    + "in infiniteOrderDeriv.tex, lines 154–159, on the positive half-line, "
                    + "and includes the degree bound n = 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The signed derivative regions descend to complete monotonicity"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix a real polynomial p. Define polynomials q₀ = p and "
                        + "qⱼ₊₁ = ((↑j : ℝ) + 1)qⱼ − qⱼ′, with j a natural number included "
                        + "in the real scalars. Induction gives "
                        + "(−1)ʲ f⁽ʲ⁾(x) = (x⁻¹)ʲ⁺¹ qⱼ(log x) for x > 0, "
                        + "where f(x) = p(log x)/x. At order zero this is division by x. "
                        + "For the next order, differentiate the identity on a neighborhood "
                        + "inside the positive half-line. The product rule for the inverse "
                        + "power and the chain rule for the polynomial composed with log "
                        + "give precisely the recurrence for qⱼ₊₁.")),
                    Paragraph(Text(
                        "The factor (x⁻¹)ʲ⁺¹ is strictly positive. Evaluating at x = exp y "
                        + "shows that nonnegativity of the signed jth derivative on x > 0 "
                        + "implies qⱼ(y) ≥ 0 for every real y. Conversely, nonnegativity "
                        + "of qⱼ on the real line implies the signed derivative inequality "
                        + "by multiplication by that positive factor. The degree bound "
                        + "on p is retained in both directions.")),
                    Paragraph(Text(
                        "A polynomial nonnegative on the real line has nonnegative "
                        + "leading coefficient. For natural degree zero, write it as a "
                        + "constant and evaluate at zero. For positive degree, a negative "
                        + "leading coefficient would make its values tend to minus infinity "
                        + "as the argument tends to plus infinity, contradicting nonnegativity.")),
                    Paragraph(Text(
                        "Now let a > 0 and suppose r = aq − q′ is nonnegative everywhere. "
                        + "If q has natural degree zero, r = aq and division by a gives "
                        + "q ≥ 0. Otherwise q′ has smaller degree than aq, so r has the "
                        + "same degree as q and leading coefficient a times that of q. "
                        + "The leading-coefficient observation applied to r gives a "
                        + "nonnegative leading coefficient for q. Applying it to r(−y), "
                        + "and using the common degree and the sign of the leading "
                        + "coefficient under y ↦ −y, gives a nonnegative leading "
                        + "coefficient for q(−y) as well.")),
                    Paragraph(Text(
                        "Positive degree makes both of these nonnegative leading "
                        + "coefficients nonzero and hence positive. Consequently q tends "
                        + "to plus infinity at both ends of the real line. Continuity "
                        + "then gives a global minimum at some m. "
                        + "Fermat's theorem gives q′(m) = 0, so "
                        + "0 ≤ r(m) = aq(m). Since a is positive, q(m) ≥ 0; "
                        + "the minimum property yields q(y) ≥ 0 for every y.")),
                    Paragraph(Text(
                        "Apply this implication with q = qₖ and a = (↑k : ℝ) + 1. "
                        + "Nonnegativity of qₖ₊₁ implies nonnegativity of qₖ. "
                        + "Transferring back to derivatives proves inclusion of the "
                        + "region of order k + 1 in the region of order k for every "
                        + "natural k, and hence for every k at least one.")),
                    Paragraph(Text(
                        "Finally, membership in all regions of positive order supplies "
                        + "every positive-order sign inequality. Membership in the region "
                        + "of order one, followed by the inclusion at k = 0, supplies "
                        + "the zeroth-order inequality. Thus all orders satisfy the "
                        + "complete monotonicity predicate. In the reverse direction, "
                        + "that predicate supplies the sign inequality at each order, "
                        + "and the given degree bound supplies the remaining condition "
                        + "for membership. Combining this equivalence with the inclusions "
                        + "proves both assertions for each n."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ma-weigert-2025-log-function-monotone-chain"),
                    ResolutionKind.Proved)))));

    private static Formula LogFunctionDefinition() => All("p", Polynomials(),
        All("x", Reals(), Equal(LocalCall("logFunction", X("p"), X("x")),
            new Formula.Fraction(
                At(Qualified("Polynomial", "eval"), At(Qualified("Real", "log"), X("x")), X("p")),
                X("x")))));

    private static Formula DerivativeRegionDefinition() => All("n", Naturals(), All("k", Naturals(),
        Equal(LocalCall("derivativeRegion", X("n"), X("k")),
            Seq(OpenBrace, Typed(X("p"), Polynomials()), Sp, Mid, Sp,
                Conjunction(DegreeBound(), SignedCondition(LocalCall("logFunction", X("p")))),
                CloseBrace))));

    private static Formula CompletelyMonotoneDefinition() => All("f", Arrow(Reals(), Reals()),
        Equivalence(LocalCall("completelyMonotone", X("f")),
            All("k", Naturals(), SignedCondition(X("f")))));

    private static Formula ClaimBody() => All("n", Naturals(),
        Conjunction(
            All("k", Naturals(), Arrow(LE(D(1), X("k")),
                new Formula.Relation(
                    LocalCall("derivativeRegion", X("n"), Add(X("k"), D(1))),
                    FormulaRelationOperator.SubsetOf,
                    LocalCall("derivativeRegion", X("n"), X("k"))))),
            All("p", Polynomials(), Arrow(DegreeBound(),
                Equivalence(
                    All("k", Naturals(), Arrow(LE(D(1), X("k")),
                        new Formula.Relation(X("p"), FormulaRelationOperator.MemberOf,
                            LocalCall("derivativeRegion", X("n"), X("k"))))),
                    LocalCall("completelyMonotone", LocalCall("logFunction", X("p"))))))));

    private static Formula DegreeBound() => LE(At(Qualified("Polynomial", "natDegree"), X("p")), X("n"));
    private static Formula SignedCondition(Formula f) => All("x", Reals(),
        Arrow(LT(Typed(D(0), Reals()), X("x")),
            LE(Typed(D(0), Reals()), Multiply(
                new Formula.Power(Parenthesized(Typed(new Formula.Negate(D(1)), Reals())), X("k")),
                At(Qualified("iteratedDeriv"), X("k"), f, X("x"))))));

    private static Formula Local(string name) => Qualified("D5", "S3", "Analytic", "LogFunctionMonotoneChain", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Polynomials() => At(Qualified("Polynomial"), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
