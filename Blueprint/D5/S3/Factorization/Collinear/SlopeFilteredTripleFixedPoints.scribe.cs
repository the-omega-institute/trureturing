using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Collinear;

internal sealed class SlopeFilteredTripleFixedPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed points of three-abscissa translation after filtering by a slope.",
        H("Slope-Filtered Triple Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slope-filtered-triple-fixed-points"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Collinear/SlopeFilteredTripleFixedPoints.card_fixedBy_nonzero"),
                H("Exact fixed-point count for a nonzero translation"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A slope-admissible triple is a three-element abscissa set on which "
                    + "multiplication by the slope is injective. Translation preserves "
                    + "this condition. A fixed triple is a three-cycle, which exists "
                    + "only when the translation has order three. Its image remains "
                    + "three distinct points exactly when the slope does not kill the "
                    + "translation direction. All fixed triples form one translation "
                    + "orbit, whose stabilizer has order three."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var a = F.Id("a");
        var t = F.Id("t");
        var fixedCount = Call("card", Call("fixedBy", Call("SlopeTriple", n, a), t));
        var nonzero = new Formula.Relation(t, FormulaRelationOperator.NotEqual, D(0));
        var torsion = new Formula.Relation(Seq(D(3), t), FormulaRelationOperator.Equal, D(0));
        var notTorsion = new Formula.Relation(Seq(D(3), t), FormulaRelationOperator.NotEqual, D(0));
        var survives = new Formula.Relation(Seq(a, t), FormulaRelationOperator.NotEqual, D(0));
        var killed = new Formula.Relation(Seq(a, t), FormulaRelationOperator.Equal, D(0));
        var positiveCase = new Formula.Logic(
            new Formula.Logic(nonzero, FormulaLogicOperator.And,
                new Formula.Logic(torsion, FormulaLogicOperator.And, survives)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(fixedCount, FormulaRelationOperator.Equal,
                new Formula.Fraction(n, D(3))));
        var zeroCase = new Formula.Logic(
            new Formula.Logic(nonzero, FormulaLogicOperator.And,
                new Formula.Logic(notTorsion, FormulaLogicOperator.Or, killed)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(fixedCount, FormulaRelationOperator.Equal, D(0)));
        return new Formula.Logic(positiveCase, FormulaLogicOperator.And, zeroCase);
    }
}
