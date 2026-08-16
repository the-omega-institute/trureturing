using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class RadixTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var b = Id("b");
        var q = Id("Q");
        var naturals = Id("N");
        var half = new Formula.Fraction(Num(1), Num(2));
        var denominator = Add(b, Num(1));
        var threshold = new Formula.Fraction(b, Multiply(Num(2), denominator));
        var scale = new Formula.Power(b, q);
        var unitPoint = new Formula.Fraction(Num(1), denominator);
        var evenPoint = new Formula.Fraction(new Formula.Fraction(b, Num(2)), denominator);
        var eventualLowerBounds = Call("eventualLowerBounds", b);

        Formula Arm(Formula point, Formula value) => Equal(
            Multiply(scale, Call("radixDistance", b, q, point)),
            value);

        var assumptions = new Formula.Logic(
            new Formula.Relation(
                b,
                FormulaRelationOperator.GreaterThanOrEqual,
                Num(2)),
            FormulaLogicOperator.And,
            new Formula.Relation(
                q,
                FormulaRelationOperator.GreaterThanOrEqual,
                Num(1)));
        var oddRow = new Formula.Logic(
            Call("Odd", b),
            FormulaLogicOperator.Implies,
            Equal(Call("sSup", eventualLowerBounds), half));
        var evenRow = new Formula.Logic(
            Call("Even", b),
            FormulaLogicOperator.Implies,
            new Formula.Logic(
                Arm(evenPoint, threshold),
                FormulaLogicOperator.And,
                Equal(Call("sSup", eventualLowerBounds), threshold)));
        var table = new Formula.Logic(
            Arm(unitPoint, unitPoint),
            FormulaLogicOperator.And,
            new Formula.Logic(oddRow, FormulaLogicOperator.And, evenRow));
        var statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, table));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The constant arm and exact odd/even radix champions form one packaged table.",
            H("Radix Champion Table"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("radix-champion-table"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/RadixTable.radix_champion_table"),
                    H("Radix champion table"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every radix b at least two and positive level Q, the reciprocal "
                        + "point has its exact constant arm. Odd radices have champion supremum "
                        + "one half, attained in the frozen source theorem by x equal to one "
                        + "half. Even radices have both the exact half-radix constant arm and "
                        + "the matching exact champion supremum.")),
                        Paragraph(Text(
                            "This declaration is only a conjunction packaging four frozen "
                            + "theorems for single-GID coverage; it contains no new mathematics."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ConstantArms")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ChampionExtremality")),
            ]));
    }
}
