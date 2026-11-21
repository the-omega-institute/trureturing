using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletRampEndpointDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletRampEndpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic derivative at one from a finite Mangoldt ramp",
        H("The endpoint comparison"),
        Blocks(
            Paragraph(Text("Let χ be a nonprincipal complex Dirichlet character of positive modulus N. "
                + "Write D for L′(1,χ)/L(1,χ). For real x the host readout g(x) is xD plus the sum of "
                + "Λ(n)χ(n) max(x/n − 1, 0) over positive integers n ≤ x. Let γ be Euler’s constant "
                + "and let T(x) be the integral of (ψ(u) − u)/u² over u > x, where ψ is the inclusive "
                + "Chebyshev sum over prime powers.")),
            Describe.Lean(DescribeId.Create("finite-endpoint"), DeclarationHandle.Create(Module + "logDerivative_le_ramp_tail"),
                H("A signed tail bound for every real endpoint x ≥ 2"),
                StatementSource.FromAuthor(F.Disp(Le(Call("abs", F.Id("D")),
                    F.Seq(Call("abs", Call("g", F.Id("x"))), F.Slash, F.Id("x"), F.Plus,
                        MainTerm(), F.Minus, Call("T", F.Id("x")))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At each included integer n, the positive part equals x/n − 1, "
                        + "including its zero value when n = x. The character has norm at most one. "
                        + "After division by x the norm of its ramp is at most the sum of Λ(n)/n "
                        + "minus ψ(x)/x. The complete Chebyshev tail identity evaluates this difference "
                        + "as log x − 1 − γ − T(x). Subtract the ramp from g(x) and apply the triangle inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-threshold"), DeclarationHandle.Create(Module + "uniform_logDerivative_of_ramp"),
                H("An additive bound uniform in the modulus and character"),
                StatementSource.FromAuthor(F.Disp(new Formula.Logic(
                    Le(Call("abs", Call("g", F.Id("x"))), F.Seq(F.Id("x"), F.Caret, F.Grp(
                        F.Seq(F.D(1), F.Slash, F.D(2), F.Plus, F.Id("epsilon"))))),
                    FormulaLogicOperator.Implies,
                    Le(Call("abs", F.Id("D")), F.Seq(MainTerm(), F.Plus, F.Id("eta")))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real ε < 1/2 and η > 0 there is a real X ≥ 2 such that "
                        + "the implication holds for every real x ≥ X and every nonprincipal χ of "
                        + "every positive modulus. Division of the assumed bound by x gives x raised "
                        + "to ε − 1/2. This power tends to zero, as does the signed integral T(x). "
                        + "Choose one threshold beyond which each contributes at most η/2."))),
                DescribeRole.Theorem))));

    private static Formula MainTerm() => F.Seq(Call("log", F.Id("x")), F.Minus, F.D(1), F.Minus, F.Id("gamma"));
    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
