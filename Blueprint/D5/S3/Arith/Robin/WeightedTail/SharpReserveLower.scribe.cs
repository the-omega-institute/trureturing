using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.WeightedTail;

internal sealed class SharpReserveLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict all-integer lower reserve for the Robin log margin",
        H("The reserve above the weighted Chebyshev tail"),
        Blocks(Describe.Lean(DescribeId.Create("sharp-lower-reserve-all-integers"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/WeightedTail/SharpReserveLower.sharp_lower_reserve_all_integers"),
            H("Lower coefficient 2√2 − 2 at the logarithmic clock"),
            StatementSource.FromAuthor(Reserve()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Here J(y) is weightedTail psiErrorKernel y. For every positive ε, "
                    + "one real threshold Y ≥ 16 gives the strict reserve at every natural n with "
                    + "log(n) ≥ Y.")),
                Paragraph(Text("For y = log(n), a prime between √y and y/2 pays through its missing "
                    + "first power, its valuation-one Euler gap, or its extra square. In all three "
                    + "cases the payment is bounded below by the minimum of 1/(2p(p+1)) and "
                    + "1/(2y) − 1/(2p²). Distinct primes charge distinct terms of the exact ledger.")),
                Paragraph(Text("The prime number theorem gives the limiting prime count on each "
                    + "fixed shell at scale √y. Nested finite shells below and above p/√y = √2 "
                    + "give lower contributions arbitrarily close to 3/√2 − 2 and 1/√2, respectively, "
                    + "after multiplication by √y log(y). Their sum is 2√2 − 2. Fixing the shells "
                    + "before taking y large leaves room for the strict inequality.")),
                Paragraph(Text("Independent derivation from the Robin ledger and the unconditional "
                    + "prime number theorem, with no priority claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);

    private static Formula Reserve()
    {
        var epsilon = F.Id("epsilon");
        var threshold = F.Id("Y");
        var n = F.Id("n");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var natural = Seq(Mathbb, Grp(F.Id("N")));
        var y = Call("log", n);
        var numerator = Subtract(Subtract(Multiply(D(2), Seq(Sqrt, Grp(D(2)))), D(2)), epsilon);
        var denominator = Multiply(Seq(Sqrt, Grp(y)), Call("log", y));
        var strictBound = new Formula.Relation(new Formula.Fraction(numerator, denominator),
            FormulaRelationOperator.LessThan, Subtract(Call("robinLogMargin", n), Call("J", y)));
        var allIntegers = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            natural, new Formula.Logic(
                new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, y),
                FormulaLogicOperator.Implies, strictBound));
        var thresholdExists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("Y"),
            real, new Formula.Logic(
                new Formula.Relation(D(1, 6), FormulaRelationOperator.LessThanOrEqual, threshold),
                FormulaLogicOperator.And, allIntegers));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("epsilon"),
            real, new Formula.Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, epsilon),
                FormulaLogicOperator.Implies, thresholdExists)));
    }
}
