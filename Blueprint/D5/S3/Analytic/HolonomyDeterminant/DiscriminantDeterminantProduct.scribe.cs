using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HolonomyDeterminant;

internal sealed class DiscriminantDeterminantProductDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct."
            + "discriminant_determinant_product";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two mod-five sine determinants have golden ratio and discriminant product.",
        H("Discriminant Determinant Product"),
        Blocks(Describe.Lean(
            DescribeId.Create("discriminant-determinant-product"),
            DeclarationHandle.Create(Declaration),
            H("The mod-five sector determinants recover the golden constants"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two source sectors are represented by two times sine of pi over five "
                        + "and two times sine of two pi over five. Their product is the square "
                        + "root of five.")),
                Paragraph(Text(
                    "Ordering the second sector over the first gives the golden ratio. The proof "
                        + "uses the exact fifth-angle cosine value and the sine double-angle "
                        + "identity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula firstSector = Seq(
            D(2), Sp, Times, Sp,
            Call("sin", new Formula.Fraction(Pi, D(5))));
        Formula secondSector = Seq(
            D(2), Sp, Times, Sp,
            Call("sin", new Formula.Fraction(Seq(D(2), Sp, Times, Sp, Pi), D(5))));
        Formula productIdentity = EqualTo(
            Seq(Grp(firstSector), Sp, Times, Sp, Grp(secondSector)),
            Call("sqrt", D(5)));
        Formula ratioIdentity = EqualTo(
            new Formula.Fraction(secondSector, firstSector),
            F.Id("goldenRatio"));

        return Disp(And(productIdentity, ratioIdentity));
    }

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
