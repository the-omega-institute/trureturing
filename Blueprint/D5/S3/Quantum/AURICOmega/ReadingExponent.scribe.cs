using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class ReadingExponentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/ReadingExponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A function multiplicative on [0, 1] with F(cos t) + F(sin t) = 1 on the quarter circle is the square, without any continuity assumption.",
        H("The reading exponent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reading-exponent-square"),
                DeclarationHandle.Create(Module + "eq_sq_of_mul_of_cos_add_sin"),
                H("Multiplicativity and quarter-circle normalization force the square"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a real function on the real line. Assume F(st) = F(s)F(t) for all "
                        + "s and t in [0, 1], and F(cos t) + F(sin t) = 1 for every t in [0, π/2]. "
                        + "Then F(s) = s² for every s in [0, 1]. No continuity, measurability or "
                        + "monotonicity of F is assumed, and nothing is asserted about F outside "
                        + "[0, 1].")),
                    Paragraph(Text(
                        "Proof: since F(s) = F(√s)², F is nonnegative on [0, 1], and the "
                        + "normalization at the angle arccos s reads F(s) + F(√(1 − s²)) = 1, so "
                        + "F ≤ 1 there. The normalization at t = 0 gives F(1) + F(0) = 1, and "
                        + "F(0) = F(0)² = F(0)F(1) excludes F(0) = 1, so F(0) = 0 and F(1) = 1. For "
                        + "0 ≤ s ≤ t ≤ 1 with t > 0, F(s) = F(t)F(s/t) ≤ F(t), so F is monotone on "
                        + "[0, 1]. The function G(u) = F(√u) satisfies G(u) + G(1 − u) = 1 on [0, 1] "
                        + "and is multiplicative there; hence G(1/2) = 1/2, and induction on n gives "
                        + "G(k/2ⁿ) = k/2ⁿ for 0 ≤ k ≤ 2ⁿ: a point k/2ⁿ⁺¹ with k ≤ 2ⁿ is (1/2)(k/2ⁿ), "
                        + "and the remaining points are reached through G(u) + G(1 − u) = 1. "
                        + "Monotonicity and the dyadic values give u − 1/2ⁿ < G(u) for every n; the "
                        + "same bound for 1 − u together with G(u) + G(1 − u) = 1 gives "
                        + "G(u) < u + 1/2ⁿ. Hence G(u) = u, and F(s) = G(s²) = s².")),
                    Paragraph(Text(
                        "Neither hypothesis can be dropped. The polynomial 3s⁴ − 2s⁶ satisfies the "
                        + "normalization, since with a = cos² t and b = sin² t one has "
                        + "3(a² + b²) − 2(a³ + b³) = 3(1 − 2ab) − 2(1 − 3ab) = 1, but it is not "
                        + "multiplicative: its value at 1/4 is 46/4096, while the square of its "
                        + "value at 1/2 is 100/4096. The power s ↦ sᵖ is multiplicative for every "
                        + "p, but for p ≠ 2 the normalization fails at t = π/4, where the sum is "
                        + "2^(1 − p/2) ≠ 1.")),
                    Paragraph(Text(
                        "The result is an elementary functional-equation argument; no published "
                        + "source stating it in this form is known, and nothing is claimed as "
                        + "new."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);

    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula TheoremFormula()
    {
        Formula s = V("s"), t = V("t");
        Formula unit = Call("Icc", D(0), D(1));
        Formula quarter = Call("Icc", D(0), new Formula.Fraction(Pi, D(2)));
        Formula Fn(Formula x) => Call("F", x);

        Formula hmul = All("s", unit, All("t", unit,
            Equal(Fn(new Formula.Binary(s, FormulaBinaryOperator.Multiply, t)),
                new Formula.Binary(Fn(s), FormulaBinaryOperator.Multiply, Fn(t)))));
        Formula hnorm = All("t", quarter,
            Equal(new Formula.Binary(Fn(Call("cos", t)), FormulaBinaryOperator.Add,
                Fn(Call("sin", t))), D(1)));
        Formula conclusion = All("s", unit, Equal(Fn(s), new Formula.Power(s, D(2))));

        return Disp(All("F", new Formula.TypeArrow(Reals, Reals),
            Implies(hmul, Implies(hnorm, conclusion))));
    }
}
