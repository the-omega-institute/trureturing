using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletZeroBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse-square budget for every Dirichlet zero",
        H("Ordinary zeros with their full multiplicities"),
        Blocks(
            Describe.Lean(DescribeId.Create("completion-budget"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletZeroBounds.completionBudget"),
                H("The corrected completed-zero budget"),
                StatementSource.FromAuthor(BudgetDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a be zero for an even character and one otherwise. "
                    + "Uχ(t) = (log(q)-log(π)+log(|t|+3)-log(2)+1/2 "
                    + "- Re(1/(2+a+it)))/2 + K₀, with "
                    + "K₀ = log(2)/4+4log(3)/9+1/3 < 1. The real Gamma correction "
                    + "and the explicit arithmetic constant remain visible. The logarithmic "
                    + "series bound separates the terms at two and three. Mathlib's "
                    + "log_div_self_rpow_antitoneOn and sum_le_integral compare each "
                    + "finite tail with an integral. WeightedStieltjes's public "
                    + "intervalIntegral_log_add_two_div_sq_eq evaluates it, and its "
                    + "nonnegative endpoint remainder gives (1+log(3))/3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-square-bound"),
            DeclarationHandle.Create("D5/S3/CharacterSums/DirichletZeroBounds.zero_square_bound"),
            H("The full zero budget"), StatementSource.FromAuthor(Claim()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let χ be a primitive nonprincipal complex Dirichlet "
                    + "character modulo a positive q. For any real T and t with |t| ≤ T, "
                    + "all ordinary L-function zeros have real part strictly below one. "
                    + "Their inverse-square sum at 2+it, with analytic multiplicity, "
                    + "is summable and at most log(q(T+3))+4. The height condition "
                    + "already forces T ≥ 0; no separate assumption is needed.")),
                Paragraph(Text("The ordinary zero divisor is the disjoint union of "
                    + "the completed zero divisor in the open critical strip and "
                    + "the simple parity lattice -a-2n, where a is zero for an even "
                    + "character and one otherwise. The explicit bijection preserves "
                    + "the completed multiplicities and assigns multiplicity one "
                    + "to each parity zero, including zero for even characters.")),
                Paragraph(Text("The completed contribution is at most Uχ(t) and strictly "
                    + "below log(q(|t|+3))/2 + 5/4. For the lattice, the real distance "
                    + "is at least 2(n+1). The integral test gives "
                    + "Σ (n+1)^(-2) ≤ 2, so its contribution is at most 1/2. "
                    + "The full sum is therefore at most Uχ(t)+1/2 and strictly below "
                    + "log(q(|t|+3))/2 + 7/4. Logarithmic monotonicity and q ≥ 1 "
                    + "give the common height budget log(q(T+3))+4. All three "
                    + "bounds are included in the public conclusion.")),
                Paragraph(Text("This theorem concerns all zeros of the actual "
                    + "Dirichlet L-function, including every trivial zero. It is a "
                    + "uniform analytic budget and supplies no one-sided arithmetic "
                    + "moment inequalities."))), DescribeRole.Theorem))));

    private static Formula BudgetDefinition()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var t = F.Id("t");
        var point = At("add", F.D(2), At("add", At("parity", c),
            At("mul", At("realToComplex", t), At("imaginaryUnit"))));
        var correction = At("re", At("inverse", point));
        var numerator = At("sub", At("add", At("sub", At("add",
            At("sub", At("log", q), At("log", At("pi"))),
            At("log", At("add", At("abs", t), F.D(3)))), At("log", F.D(2))),
            At("div", F.D(1), F.D(2))), correction);
        var constant = At("add", At("div", At("log", F.D(2)), F.D(4)),
            At("add", At("div", At("mul", F.D(4), At("log", F.D(3))), F.D(9)),
                At("div", F.D(1), F.D(3))));
        var value = At("add", At("div", numerator, F.D(2)), constant);
        return F.Disp(All("q", At("Naturals"),
            All("chi", At("ComplexDirichletCharacters", q), All("t", At("Reals"),
                Equal(At("completionBudget", c, t), value)))));
    }

    private static Formula Claim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var t = F.Id("t");
        var height = F.Id("T");
        var sum = At("weightedInverseSquareSum", At("LFunction", c), t);
        var bound = At("add", At("log", At("mul", q,
            At("add", height, F.D(3)))), F.D(4));
        var precise = At("add", At("div", At("log", At("mul", q,
            At("add", At("abs", t), F.D(3)))), F.D(2)), At("div", F.D(7), F.D(4)));
        var corrected = At("add", At("completionBudget", c, t), At("half"));
        var conclusion = At("and", At("ZeroRealPartsStrictlyBelowOne", c),
            At("and", At("SummableInverseSquares", At("LFunction", c), t),
                At("and", At("lt", sum, precise), At("and", At("le", sum, bound),
                    At("le", sum, corrected)))));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q),
                At("implies", At("primitiveNonprincipal", c),
                    All("T", At("Reals"), All("t", At("Reals"),
                        At("implies", At("le", At("abs", t), height), conclusion)))))));
    }
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
