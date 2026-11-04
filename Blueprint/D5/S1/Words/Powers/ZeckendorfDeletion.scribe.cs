using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class ZeckendorfDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Powers/ZeckendorfDeletion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting the least significant Fibonacci position recovers the index of the containing golden substitution block.",
        H("Literal Zeckendorf deletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("literal-deletion"),
                DeclarationHandle.Create(Prefix + "deleteLeast"), H("Delete a position and decode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the canonical occupied Fibonacci indices, whose weights start at F_2=1 and F_3=2. Remove index 2, subtract one from each remaining index, and sum the resulting Fibonacci weights. Removing the position is different from retaining its weight as F_1. This is the literal operation defining OEIS A319433, with its original index including zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deletion-block"),
                DeclarationHandle.Create(Prefix + "deletion_block"), H("The block containing an index"),
                StatementSource.FromAuthor(Disp(Bound("n", Naturals(),
                    And(LessEqual(Call("goldenSubstStart", Call("deleteLeast", F.Id("n"))), F.Id("n")),
                        Less(F.Id("n"), Call("goldenSubstStart", Add(Call("deleteLeast", F.Id("n")), D(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A block start shifts all canonical occupied indices upward by one, so deletion recovers its source index. A second position exists exactly when the source has no occupied index 2. Its canonical digits append index 2 to the shifted list, and deletion removes precisely that appended digit. The existing substitution blocks cover every natural index, establishing both interval inequalities without defining deletion by a floor formula."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bound(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
}
