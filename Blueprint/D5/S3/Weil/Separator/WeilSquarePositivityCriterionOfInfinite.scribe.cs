using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class WeilSquarePositivityCriterionOfInfiniteDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assuming infinitely many nontrivial zeros, the Riemann hypothesis is equivalent "
            + "to repository Weil-square positivity for every ZeroData and for some ZeroData.",
        H("Weil-Square Positivity Criteria Under Infinitely Many Zeros"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rh-iff-forall-zero-data-weil-square-positivity"),
                DeclarationHandle.Create(
                    Prefix + "rh_iff_forall_zeroData_weilSquarePositivity"),
                H("RH is equivalent to positivity for every ZeroData"),
                StatementSource.FromAuthor(ForallFormula()),
                AssessedProvenance.FromRepo(),
                ExplanatoryBlocks(),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-exists-zero-data-weil-square-positivity"),
                DeclarationHandle.Create(
                    Prefix + "rh_iff_exists_zeroData_weilSquarePositivity"),
                H("RH is equivalent to positivity for some ZeroData"),
                StatementSource.FromAuthor(ExistsFormula()),
                AssessedProvenance.FromRepo(),
                ExplanatoryBlocks(),
                DescribeRole.Theorem)),
        []));

    private static BlockSequence ExplanatoryBlocks() => Blocks(
        Paragraph(Text(
            "The hypothesis hInf is M1-b, infinitely many nontrivial zeros, and is not "
                + "proved in this repository. The ZeroData construction used behind M1-a "
                + "is noncomputable and depends on Classical.choice.")),
        Paragraph(Text(
            "The right side is this repository's Weil-square positivity for zeroSum and "
                + "convolutionSquare. The results bind the frozen fixed-Z criterion and "
                + "nonemptiness bridge; these conditional equivalences are not a proof of RH.")));

    private static Formula ForallFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula allZeroData = ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Positivity(zeroData));

        return Criterion(allZeroData);
    }

    private static Formula ExistsFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula someZeroData = Exists(
            [Bound("Z", F.Id("ZeroData"))],
            Positivity(zeroData));

        return Criterion(someZeroData);
    }

    private static Formula Criterion(Formula positivity) =>
        Disp(Implies(
            InfiniteNontrivialZeros(),
            Iff(RiemannHypothesis(), positivity)));

    private static Formula InfiniteNontrivialZeros()
    {
        Formula rho = Rho;
        Formula zeroSet = Seq(
            OpenBrace, rho, Sp, Mid, Sp, Call("IsNontrivialZero", rho), CloseBrace);

        return Call("Infinite", zeroSet);
    }

    private static Formula Positivity(Formula zeroData)
    {
        Formula test = F.Id("g");
        Formula witness = F.Id("hZero");
        Formula square = Call("convolutionSquare", test);
        Formula zeroSide = Call("zeroSum", zeroData, square, witness);

        return ForAll(
            [
                Bound("g", F.Id("WeilTestFunction")),
                Bound("hZero", Call("SymmetricConvergent", zeroData, square)),
            ],
            LessOrEqual(D(0), RealPart(zeroSide)));
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
