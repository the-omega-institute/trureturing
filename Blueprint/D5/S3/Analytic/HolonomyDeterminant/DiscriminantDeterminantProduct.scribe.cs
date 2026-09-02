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
        "Conditional Lerch data identify the two mod-five holonomy determinants.",
        H("Discriminant Determinant Product"),
        Blocks(Describe.Lean(
            DescribeId.Create("discriminant-determinant-product"),
            DeclarationHandle.Create(Declaration),
            H("The mod-five sector determinants recover the golden constants"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assuming the reflected Hurwitz derivative formula at both source-fixed "
                        + "mod-five representatives, the frozen determinant bridge evaluates "
                        + "the two zeta-regularized massless holonomy determinants.")),
                Paragraph(Text(
                    "Their product is the square root of five, while ordering the second sector "
                        + "over the first gives the golden ratio."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula firstHolonomy = new Formula.Fraction(D(1), D(5));
        Formula secondHolonomy = new Formula.Fraction(D(2), D(5));
        Formula firstSector = Call("masslessHolonomyDeterminant", firstHolonomy);
        Formula secondSector = Call("masslessHolonomyDeterminant", secondHolonomy);
        Formula lerchPremises = And(
            Call("HasReflectedHurwitzDerivativeAtZeroFormula", firstHolonomy),
            Call("HasReflectedHurwitzDerivativeAtZeroFormula", secondHolonomy));
        Formula productIdentity = EqualTo(
            Seq(Grp(firstSector), Sp, Times, Sp, Grp(secondSector)),
            Call("sqrt", D(5)));
        Formula ratioIdentity = EqualTo(
            new Formula.Fraction(secondSector, firstSector),
            F.Id("goldenRatio"));

        return Disp(Implies(lerchPremises, And(productIdentity, ratioIdentity)));
    }

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

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
