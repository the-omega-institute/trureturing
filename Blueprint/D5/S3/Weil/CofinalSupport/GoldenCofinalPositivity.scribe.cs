using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CofinalSupport;

internal sealed class GoldenCofinalPositivityDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.golden_cofinal_positivity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity on cofinal golden support layers reaches every compact Weil test.",
        H("Golden Cofinal Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cofinal-positivity"),
            DeclarationHandle.Create(Handle),
            H("Cofinal support-layer positivity is global"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The carrier is the canonical compactly supported Weil-test space. "
                    + "The radius at level n is L0 times phi to the power 2n, and "
                    + "supportLayer(R) consists exactly of tests whose function support "
                    + "is contained in [-R,R]. If these radii tend to infinity and Q is "
                    + "nonnegative on every corresponding layer, then Q is nonnegative "
                    + "on every Weil test."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat"), real = Call("Real");
        Formula test = Call("WeilTestFunction");
        Formula initial = F.Id("L0"), q = F.Id("Q");
        Formula n = F.Id("n"), f = F.Id("f");

        Formula radius = Call("goldenSupportRadius", initial, n);
        Formula layer = Call("supportLayer", radius);
        Formula cofinal = Call(
            "Tendsto",
            Call("goldenSupportRadius", initial),
            Call("atTop"),
            Call("atTop"));
        Formula layerPositive = ForAll(
            [Bound("n", natural), Bound("f", test)],
            Implies(
                Seq(f, Sp, InMacro, Sp, layer),
                LessOrEqual(D(0), Apply(q, f))));
        Formula globalPositive = ForAll(
            [Bound("f", test)],
            LessOrEqual(D(0), Apply(q, f)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, initial, Colon, Sp, real, Comma),
            Seq(q, Colon, Sp, new Formula.TypeArrow(test, real), Comma),
            Seq(All(cofinal, layerPositive), Sp, Rightarrow),
            Seq(globalPositive, Dot),
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
