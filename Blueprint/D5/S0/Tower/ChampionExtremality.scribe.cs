using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class ChampionExtremalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var b = Id("b");
        var q = Id("Q");
        var y = Id("y");
        var naturals = Id("N");
        var reals = Id("R");
        var half = new Formula.Fraction(Num(1), Num(2));
        var evenThreshold = new Formula.Fraction(
            b,
            Multiply(Num(2), Add(b, Num(1))));
        var halfPoint = half;
        var eventualLowerBounds = Call("eventualLowerBounds", b);

        Formula Arm(Formula level, Formula point) => Multiply(
            new Formula.Power(b, level),
            Call("radixDistance", b, level, point));

        Formula ForBase(Formula assumptions, Formula conclusion) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("b"),
            naturals,
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));

        Formula BaseParityAssumptions(string parity) => new Formula.Logic(
            new Formula.Relation(
                b,
                FormulaRelationOperator.GreaterThanOrEqual,
                Num(2)),
            FormulaLogicOperator.And,
            Call(parity, b));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/ChampionExtremality",
                "Integer radix towers have exact odd and even champion arms."),
            H("Radix Champion Extremality"),
            Blocks(
                Paragraph(Text(
                    "For a radix b, eventualLowerBounds(b) is the set of real r for which "
                    + "there are a real point x and a natural level N such that every Q at "
                    + "least N satisfies r less than or equal to b to the Q times "
                    + "radixDistance(b,Q,x). Its supremum is the supremum over points of the "
                    + "liminf normalized distance, written in the equivalent eventual-tail "
                    + "form used by the Lean declarations.")),
                DocumentBlock.Describe.Lemma(
                    DescribeId.Create("one-even-radix-step-exits-the-forbidden-band"),
                    H("One even-radix step exits the forbidden band"),
                    LeanTheorem("D5/S0/Tower/ChampionExtremality.one_step_exit"),
                    ForBase(
                        BaseParityAssumptions("Even"),
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("y"),
                            reals,
                            new Formula.Logic(
                                new Formula.Relation(
                                    Call("radixDistance", b, Num(0), y),
                                    FormulaRelationOperator.GreaterThan,
                                    evenThreshold),
                                FormulaLogicOperator.Implies,
                                new Formula.Relation(
                                    Call("radixDistance", b, Num(0), Multiply(b, y)),
                                    FormulaRelationOperator.LessThan,
                                    evenThreshold)))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If the nearest-integer distance of y is strictly above the even "
                        + "threshold, multiplying y once by b puts its nearest-integer "
                        + "distance strictly below that threshold. The proof compares to the "
                        + "explicit integers plus or minus b over two and uses the identity "
                        + "b times the threshold equals b over two minus the threshold.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("the-even-radix-champion-is-the-half-radix-arm"),
                    H("The even-radix champion is the half-radix arm"),
                    LeanTheorem("D5/S0/Tower/ChampionExtremality.even_champion_sup"),
                    ForBase(
                        BaseParityAssumptions("Even"),
                        Equal(Call("sSup", eventualLowerBounds), evenThreshold)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The frozen half-radix arm supplies the lower bound. Any eventual "
                        + "uniform lower bound strictly above it contradicts one-step exit "
                        + "between a tail level and its successor, so the supremum is exactly "
                        + "b divided by two times b plus one.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("the-odd-radix-half-point-has-a-constant-half-arm"),
                    H("The odd-radix half point has a constant half arm"),
                    LeanTheorem("D5/S0/Tower/ChampionExtremality.odd_half_arm"),
                    new Formula.BindMany(
                        FormulaQuantifier.ForAll,
                        [
                            new Formula.BoundVariable(FormulaIdentifier.Create("b"), naturals),
                            new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals),
                        ],
                        new Formula.Logic(
                            BaseParityAssumptions("Odd"),
                            FormulaLogicOperator.Implies,
                            Equal(Arm(q, halfPoint), half))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Every power of an odd radix is odd. After scaling the half point, "
                        + "the numerator is therefore one modulo two, so nearest-integer "
                        + "rounding leaves exactly one half at every level, including level "
                        + "zero.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("the-odd-radix-champion-is-one-half"),
                    H("The odd-radix champion is one half"),
                    LeanTheorem("D5/S0/Tower/ChampionExtremality.odd_champion"),
                    ForBase(
                        BaseParityAssumptions("Odd"),
                        Equal(Call("sSup", eventualLowerBounds), half)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Nearest-integer distance is always at most one half, giving the "
                        + "global upper bound. The constant half arm at x equal to one half "
                        + "belongs to the eventual-lower-bound set and attains the bound.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ConstantArms")),
            ]));
    }
}
