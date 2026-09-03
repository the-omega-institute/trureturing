using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GoldenEulerBetaZeckendorfDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/GoldenEulerBetaZeckendorf."
            + "golden_euler_beta_zeckendorf";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Euler exponent ledger has a closed Beatty form whose floor and jumps "
            + "are read from the canonical Zeckendorf expansion.",
        H("Golden Euler Beta Zeckendorf Ledger"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-euler-beta-zeckendorf"),
            DeclarationHandle.Create(Declaration),
            H("Least-index parity controls the golden Euler beta ledger"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural v, the frozen exponent o5Beta is the Beatty floor "
                        + "of (v+1)/phi plus v phi. For positive n, that floor is the sum "
                        + "of Fibonacci numbers obtained by lowering every index in the "
                        + "canonical Zeckendorf expansion, with a correction of one exactly "
                        + "when the least index is even.")),
                Paragraph(Text(
                    "Here zeck(n) is the canonical descending Zeckendorf index list and "
                        + "lastIdx(n) is its final, hence least, index. The same parity test "
                        + "selects the next ledger jump: phi squared for an even least index "
                        + "of v+1, and phi for an odd least index.")),
                Paragraph(Text(
                    "This result is an exponent-accounting characterization. It does not "
                        + "assert an all-order germ extraction, O-5, analytic continuation, "
                        + "or the Riemann Hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula v = Id("v");
        Formula n = Id("n");
        Formula k = Id("k");
        Formula naturals = Id("N");
        Formula phi = new Formula.Phi();

        Formula Zeck(Formula value) => Call("zeck", value);
        Formula LastIndex(Formula value) => Call("lastIdx", value);
        Formula IsEven(Formula value) => Call("Even", value);
        Formula Ite(Formula condition, Formula thenValue, Formula elseValue) =>
            Call("ite", condition, thenValue, elseValue);

        Formula closedForm = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("v"),
            naturals,
            Equal(
                Call("o5Beta", v),
                Add(
                    new Formula.Floor(new Formula.Fraction(Add(v, Num(1)), phi)),
                    Multiply(v, phi))));

        Formula shiftedFibSum = F.Seq(
            F.Sum, F.Underscore,
            F.Grp(k, F.Sp, F.InMacro, F.Sp, Zeck(n)),
            F.Sp, Call("fib", Subtract(k, Num(1))));
        Formula correction = Ite(IsEven(LastIndex(n)), Num(1), Num(0));
        Formula floorForm = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(
                    Num(0), FormulaRelationOperator.LessThan, n),
                FormulaLogicOperator.Implies,
                Equal(
                    new Formula.Floor(new Formula.Fraction(n, phi)),
                    Subtract(shiftedFibSum, correction))));

        Formula vPlusOne = Add(v, Num(1));
        Formula jumpForm = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("v"),
            naturals,
            Equal(
                Subtract(Call("o5Beta", vPlusOne), Call("o5Beta", v)),
                Ite(
                    IsEven(LastIndex(vPlusOne)),
                    new Formula.Power(phi, Num(2)),
                    phi)));

        return F.Disp(new Formula.Logic(
            closedForm,
            FormulaLogicOperator.And,
            new Formula.Logic(
                floorForm,
                FormulaLogicOperator.And,
                jumpForm)));
    }
}
