using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointQuadraticMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit quadratic scale controls the shifted discrepancy of every actual marked-cycle prefix.",
        H("Quadratic discrepancy tails for the actual cycle stream"),
        Blocks(
            Paragraph(Text("For each integer initial offset e, natural prefix length j, and tolerance delta > 0, let T(e,j,delta) be the actual stream mass of the event where the absolute value of e plus the first j discrepancy advances strictly exceeds (|e| + max(1,20/delta)^2)(j+1)^2.")),
            Describe.Lean(
                DescribeId.Create("actual-uniform-quadratic-marginal"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointQuadraticMarginal.actual_uniform_quadratic_marginal"),
                H("Explicit uniform marginal bound"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("T", F.Id("e"), F.Id("j"), F.Id("delta")),
                    FormulaRelationOperator.LessThanOrEqual, Call("ofReal", F.Id("delta"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a scale s in [0,1], the Schröder recurrence gives the shape generating function B(s) and the exact squared deficit (b-B(s))^2 = rho(1-s)(1+B(s)). After grouping the actual cycle by its fixed removal count and terminal sign, its size generating function is (B(s)+rho s)/(1-B(s)).")),
                    Paragraph(Text("Each absolute discrepancy advance is at most its cycle size. A deterministic inequality for one minus a product, applied to the discount factors of the first j sizes, bounds the tail using only their coordinate marginals. The bound is uniform in j and does not use independence between diagonal hits."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
