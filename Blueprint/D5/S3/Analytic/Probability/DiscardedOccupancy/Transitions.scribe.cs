using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyTransitionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound on early conditional variances gives a linear lower bound for the terminal variance.",
        H("Transitions of occupancy with discarded throws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("variance-lower"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower"),
                H("Variance from the early throws"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here n is the number of ordinary bins and p is the total probability of assigning a throw to an ordinary bin. The trial following x occupied bins increases the count with probability p times one minus x divided by n. The exact weighted variance recursion yields the displayed bound from the first floor of n divided by two increments."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var oneMinus = Subtract(D(1), p);
        var floor = Seq(Lfloor, Sp, new Formula.Fraction(n, D(2)), Sp, Rfloor);
        var coefficient = new Formula.Fraction(Multiply(p,
            new Formula.Power(Seq(Open, oneMinus, Close), D(3))), D(2));
        var lower = Seq(Multiply(floor, coefficient), Sp, Leq, Sp,
            Call("variance", n, p, Subtract(n, D(1))));
        return All("n", Nat, All("p", Real,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(0), Sp, Leq, Sp, p, Sp, Implies, Sp,
                p, Sp, Leq, Sp, D(1), Sp, Implies, Sp, lower)));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
}
