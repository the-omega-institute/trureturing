using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyCharacteristicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit finite word measure is the product of the individual throw measures.",
        H("Occupancy word laws and characteristic functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-product"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi"),
                H("The finite word measure is a product"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A throw is discarded with probability one minus p and each ordinary bin has mass p divided by n. The mass of a word is the product of the coordinate masses. The transition calculation for the characteristic function uses this same law and conditions on the count of occupied bins after the prefix."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var j = F.Id("j");
        var product = Seq(new Formula.Subscript(Prod, Seq(F.Id("i"), Colon, Sp, Call("Fin", j))),
            Sp, Call("toMeasure", Call("throwPMF", n, p)));
        var equation = Equal(Call("toMeasure", Call("wordPMF", n, p, j)), product);
        return All("n", Nat, All("p", Real, All("j", Nat,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(0), Sp, Leq, Sp, p, Sp, Implies, Sp,
                p, Sp, Leq, Sp, D(1), Sp, Implies, Sp, equation))));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
}
