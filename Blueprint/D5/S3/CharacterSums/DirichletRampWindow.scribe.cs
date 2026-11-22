using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletRampWindowDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletRampWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite test for the character ramp on an entire real interval",
        H("Bounds between active prime powers"),
        Blocks(
            Paragraph(Text("Let χ be a nonprincipal complex character of positive modulus. Write D for "
                + "L′(1,χ)/L(1,χ). Then g(x) is xD plus the sum of Λ(n)χ(n) max(x/n − 1,0) "
                + "over positive integers n ≤ x. Given Y ≤ Z, let S consist of Y, Z and the positive "
                + "integers strictly between them for which Λ(n)χ(n) is nonzero. All such integers "
                + "are prime powers coprime to the modulus.")),
            Describe.Lean(DescribeId.Create("concave-envelope"), DeclarationHandle.Create(Module + "concave_window_iff"),
                H("Comparison with any concave function on the window"),
                StatementSource.FromAuthor(F.Disp(Iff(All("x", F.Id("I"), Bound("x", "B")),
                    All("t", F.Id("S"), Bound("t", "B"))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here I is the real interval [Y,Z] and B is concave on I. The endpoints "
                        + "can be negative or equal. For every real x in the interval, take the closest "
                        + "members of S below and above x. The finite sum for g can use the same cutoff "
                        + "throughout that segment. Each positive-part term is affine there, vanishes there, "
                        + "or has zero coefficient. Thus g interpolates its two bounding values. Convexity "
                        + "of the complex norm and concavity of B give the bound at x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-log-test"), DeclarationHandle.Create(Module + "power_log_window_iff"),
                H("One logarithmic derivative test and a finite power-envelope test"),
                StatementSource.FromAuthor(F.Disp(Iff(All("x", F.Id("I"), And(Bound("x", "P"), Derivative("x"))),
                    And(All("t", F.Id("S"), Bound("t", "P")), Derivative("Y"))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here 0 < Y ≤ Z, P(x) = A xᵖ, 0 ≤ p ≤ 1, and A,c ≥ 0. "
                        + "The function P is concave on this interval. The derivative D uses the same χ "
                        + "and is independent of x, while c log x increases weakly. Consequently its "
                        + "single test at Y suffices. The choices A = 1 and c = 4 give the paired "
                        + "estimates used for a character host."))),
                DescribeRole.Theorem))));

    private static Formula Bound(string variable, string envelope) =>
        Le(Call("abs", Call("g", F.Id(variable))), Call(envelope, F.Id(variable)));
    private static Formula Derivative(string variable) =>
        Le(Call("abs", F.Id("D")), F.Seq(F.Id("c"), F.Sp, Call("log", F.Id(variable))));
    private static Formula All(string variable, Formula domain, Formula claim) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, claim);
    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
