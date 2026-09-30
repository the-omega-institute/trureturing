using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class HomFilteredTripleFixedPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An additive homomorphism filters three-cycle fixed points by its kernel.",
        H("Homomorphism-Filtered Triple Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hom-filtered-triple-fixed-points"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/HomFilteredTripleFixedPoints.card_fixedBy_nonzero"),
                H("Exact fixed-point count in a finite abelian group"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A homomorphism-admissible triple has three distinct images. "
                    + "Translation preserves admissibility. A nonzero fixed translation "
                    + "must have order three; its three-cycle is admissible exactly when "
                    + "the homomorphism does not kill that direction. Every fixed triple "
                    + "is a translate of the cycle, and its stabilizer has order three. "
                    + "Unlike a cyclic group, a noncyclic group can have several eligible "
                    + "order-three direction subgroups."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Statement()
    {
        var group = F.Id("G");
        var hom = F.Id("f");
        var t = F.Id("t");
        var fixedCount = Call("card", Call("fixedBy", Call("HomTriple", hom), t));
        var groupCard = Call("card", group);
        var nonzero = new Formula.Relation(t, FormulaRelationOperator.NotEqual, D(0));
        var torsion = new Formula.Relation(Seq(D(3), t), FormulaRelationOperator.Equal, D(0));
        var notTorsion = new Formula.Relation(Seq(D(3), t), FormulaRelationOperator.NotEqual, D(0));
        var survives = new Formula.Relation(Call("f", t), FormulaRelationOperator.NotEqual, D(0));
        var killed = new Formula.Relation(Call("f", t), FormulaRelationOperator.Equal, D(0));
        var positiveCase = new Formula.Logic(
            new Formula.Logic(nonzero, FormulaLogicOperator.And,
                new Formula.Logic(torsion, FormulaLogicOperator.And, survives)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(fixedCount, FormulaRelationOperator.Equal,
                new Formula.Fraction(groupCard, D(3))));
        var zeroCase = new Formula.Logic(
            new Formula.Logic(nonzero, FormulaLogicOperator.And,
                new Formula.Logic(notTorsion, FormulaLogicOperator.Or, killed)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(fixedCount, FormulaRelationOperator.Equal, D(0)));
        return new Formula.Logic(positiveCase, FormulaLogicOperator.And, zeroCase);
    }
}
