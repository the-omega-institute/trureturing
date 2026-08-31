using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LiHausdorffTriangularTransformDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/LiHausdorffTriangularTransform."
            + "li_hausdorff_triangular_transform";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Li coefficients form an invertible lower-triangular transform of trace moments.",
        H("Li-Hausdorff Triangular Transform"),
        Blocks(Describe.Lean(
            DescribeId.Create("li-hausdorff-triangular-transform"),
            DeclarationHandle.Create(Handle),
            H("Finite-prefix transform and its first inverse coordinates"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The one-indexed coefficient formula constructs a matrix on every finite "
                    + "prefix. Its entries above the diagonal vanish, while every diagonal "
                    + "entry is nonzero, so the induced vector map is bijective. Direct "
                    + "normalization of the three-dimensional prefix yields the three "
                    + "displayed inverse-coordinate identities."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real");
        Formula n = F.Id("N"), p = F.Id("p"), i = F.Id("i");
        Formula j = F.Id("j"), lambda = F.Id("lambda");
        Formula finN = Call("Fin", n), matrix = Call("liHausdorffMatrix", n);
        Formula vector = Arrow(finN, real);

        Formula lowerTriangular = ForAll(
            [Bound("N", natural)],
            Call("BlockTriangular", matrix, Call("toDual", finN)));
        Formula invertible = ForAll(
            [Bound("N", natural)],
            Call("Bijective", Call("mulVec", matrix)));

        Formula rowValue = Apply(Call("mulVec", matrix, p), i);
        Formula summand = Mul(Coefficient(i, j), Apply(p, j));
        Formula coefficientFormula = ForAll(
            [Bound("N", natural), Bound("p", vector), Bound("i", finN)],
            Equal(
                rowValue,
                Mul(Add(Val(i), D(1)), IndexedSum(j, Call("Iic", i), summand))));

        Formula finThree = Call("Fin", D(3));
        Formula threeVector = Arrow(finThree, real);
        Formula threeMatrix = Call("liHausdorffMatrix", D(3));
        Formula lambdaDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            lambda, Colon, Sp, threeVector, Sp, Eq, Sp,
            Call("mulVec", threeMatrix, p), Semi, Sp);
        Formula first = Equal(Apply(p, D(0)), Div(Apply(lambda, D(0)), D(4)));
        Formula second = Equal(
            Apply(p, D(1)),
            Div(
                Sub(Mul(D(4), Apply(lambda, D(0))), Apply(lambda, D(1))),
                D(1, 6)));
        Formula third = Equal(
            Apply(p, D(2)),
            Div(
                Sub(
                    Add(Apply(lambda, D(2)), Mul(D(1, 5), Apply(lambda, D(0)))),
                    Mul(D(6), Apply(lambda, D(1)))),
                D(6, 4)));
        Formula inverseCoordinates = ForAll(
            [Bound("p", threeVector)],
            Seq(lambdaDefinition, All(first, second, third)));

        return All(lowerTriangular, invertible, coefficientFormula, inverseCoordinates);
    }

    private static Formula Coefficient(Formula row, Formula column)
    {
        Formula rowIndex = Val(row), columnIndex = Val(column);
        Formula sign = Call("pow", Neg(D(1)), Add(columnIndex, D(2)));
        Formula fourPower = Call("pow", D(4), Add(columnIndex, D(1)));
        Formula binomial = Call(
            "choose",
            Add(Add(rowIndex, columnIndex), D(1)),
            Sub(rowIndex, columnIndex));
        return Mul(Div(Mul(sign, fourPower), Add(columnIndex, D(1))), binomial);
    }

    private static Formula IndexedSum(
        Formula index, Formula domain, Formula summand) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, summand);

    private static Formula Val(Formula index) => Call("val", index);

    private static Formula Neg(Formula value) => new Formula.Negate(value);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
