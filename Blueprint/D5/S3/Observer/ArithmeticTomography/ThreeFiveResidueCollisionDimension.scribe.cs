using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class ThreeFiveResidueCollisionDimensionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/ArithmeticTomography/ThreeFiveResidueCollisionDimension."
            + "three_five_residue_collision_and_dimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-five coordinate pair has its explicit collision, while the full system "
            + "has statistical dimension three.",
        H("Three-Five Residue Collision and Dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-five-residue-collision-and-dimension"),
                DeclarationHandle.Create(Declaration),
                H("The three-five collision accompanies dimension three"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical readings modulo three and modulo five identify zero "
                            + "with fifteen. This is the explicit collision required for the "
                            + "three-five coordinate pair.")),
                    Paragraph(Text(
                        "On the same ZMod 30 state carrier, all three prime coordinates are "
                            + "complete and every two-coordinate selection is incomplete. "
                            + "Therefore the least complete coordinate count is three."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula q3q5 = Seq(
            OpenBrace, F.Id("q3"), Comma, Sp, F.Id("q5"), CloseBrace);
        Formula collision = Call("Merges", q3q5, D(0), D(1, 5));
        Formula dimension = new Formula.Relation(
            F.Id("statisticalDimension"), FormulaRelationOperator.Equal, D(3));
        return Disp(new Formula.Logic(
            collision, FormulaLogicOperator.And, dimension));
    }
}
