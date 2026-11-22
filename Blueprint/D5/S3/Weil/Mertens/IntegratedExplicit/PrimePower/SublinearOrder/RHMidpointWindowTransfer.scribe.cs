using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMidpointWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer of weighted midpoint estimates to signed prime windows",
        H("The arithmetic limsup from a weighted midpoint comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-window-midpoint-transfer"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer.signed_window_midpoint_transfer"),
            H("The same remainder profile controls the normalized signed window"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let M(r,u,L) be the normalized exponential root average "
                    + "on [u,u+L] minus the full root signal at its midpoint. With "
                    + "s=1/2−1/(2r), write G(r,L) for L/(8s) times "
                    + "log(1/L)+log(2r)−2c+1/2 and c=(Euler's constant−1+log(2π))/2.")),
                Paragraph(Text("Q(m,r,L) is the limsup at positive infinity of the absolute "
                    + "original signed residual divided by its power gap, corrected inside "
                    + "the absolute value by μ(m+1)(m+1)/(ms) and μ(r) times the midpoint "
                    + "root signal. B(m,r,L) means the corrected absolute value is eventually bounded.")),
                Paragraph(Text("The whole weighted interval and its midpoint are continuous "
                    + "readouts of the same actual occurrence phase vector. A cofinal return "
                    + "transfers the lower comparison at the origin. The arithmetic term tends "
                    + "to zero after division by the original positive power gap."))),
            DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.Bind(kind, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var width = Id("L");
        var u = Id("u");
        var c = Id("C");
        var allowance = Multiply(c, Call("E", width));
        var baseline = Call("G", r, width);
        var widths = And(Lt(Num(0), width), Le(width, new Formula.Fraction(Num(1), Num(4))));
        var upper = Bind(FormulaQuantifier.ForAll, "u", Domain("R"),
            Le(new Formula.Absolute(Call("M", r, u, width)), Add(baseline, allowance)));
        var origin = Call("M", r, new Formula.Negate(new Formula.Fraction(width, Num(2))), width);
        var input = Bind(FormulaQuantifier.Exists, "C", Domain("R"), And(Lt(Num(0), c),
            Bind(FormulaQuantifier.ForAll, "L", Domain("R"),
                Imp(widths, And(upper, Le(Subtract(baseline, allowance), origin))))));

        var moebius = new Formula.Absolute(Call("mu", r));
        var distance = new Formula.Absolute(Subtract(Call("Q", m, r, width), Multiply(moebius, baseline)));
        var output = Bind(FormulaQuantifier.Exists, "C", Domain("R"), And(Lt(Num(0), c),
            Bind(FormulaQuantifier.ForAll, "L", Domain("R"),
                Imp(widths, And(Call("B", m, r, width), Le(distance, Multiply(moebius, allowance)))))));

        var cutoffs = And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r)));
        var realFunctions = F.Seq(Domain("R"), F.To, Domain("R"));
        return F.Disp(Imp(Id("RH"), Bind(FormulaQuantifier.ForAll, "m", Domain("N"),
            Bind(FormulaQuantifier.ForAll, "r", Domain("N"), Imp(cutoffs,
                Bind(FormulaQuantifier.ForAll, "E", realFunctions, Imp(input, output)))))));
    }
}
