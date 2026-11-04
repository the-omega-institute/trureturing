using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramDualMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramDualMetric.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-Gram dual vectors pair by the inverse-Gram metric.",
        H("Inverse-Gram Dual Metric"),
        Blocks(
            Paragraph(Text(
                "For a realizing matrix M of the six-length Gram matrix G, the dual "
                + "vectors obtained from rows of G inverse have Lorentz pairings equal "
                + "to the corresponding entries of G inverse. This is the metric identity "
                + "behind the dual basis construction.")),
            Describe.Lean(
                DescribeId.Create("length-gram-dual-metric"),
                DeclarationHandle.Create(Prefix + "dual_metric"),
                H("The dual vectors recover the inverse-Gram metric"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expand the first dual vector by its inverse-Gram coefficients. "
                    + "Lorentz symmetry and the already proved dual-pairing identity "
                    + "collapse the finite sum to the (i,j) entry of G inverse."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var M = F.Id("M");
        var i = F.Id("i");
        var j = F.Id("j");
        var gram = Call("lengthGram", l);
        var gramEntry = Eq(
            Call("lorentz", Call("row", M, i), Call("row", M, j)),
            Call("entry", gram, i, j));
        var dualEntry = Eq(
            Call("lorentz",
                Call("dualVector", gram, M, i),
                Call("dualVector", gram, M, j)),
            Call("entry", Call("inv", gram), i, j));
        return All("l", F.Id("Length6"), All("M", F.Id("Mat4"),
                Impl(
                    All("i", F.Id("Fin4"),
                        All("j", F.Id("Fin4"), gramEntry)),
                    Impl(
                        Less(Call("det", gram), F.D(0)),
                        All("i", F.Id("Fin4"),
                            All("j", F.Id("Fin4"), dualEntry))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Impl(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
