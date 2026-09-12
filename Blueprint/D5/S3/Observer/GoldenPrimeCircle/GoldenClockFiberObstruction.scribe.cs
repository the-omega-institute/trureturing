using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockFiberObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockFiberObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "On the full golden-integer carrier, the scalar readout determines the next "
                + "readout under multiplication exactly for ordinary integer multipliers.",
            H("Golden Integer Fiber Obstruction"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-full-fiber-descent"),
                    DeclarationHandle.Create(Prefix + "multiplication_descends_iff"),
                    H("Exact criterion for a single-valued quotient update"),
                    StatementSource.FromAuthor(DescentFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The carrier is dev GoldenInt: z=a+b*phi. Descends(u) means "
                                + "there exists a function f:Int->Int such that "
                                + "(u*z).b=f(z.b) for every golden integer z. The theorem "
                                + "proves this holds exactly when u.b=0.")),
                        Paragraph(Text(
                            "equal_integer_fiber identifies the whole fiber above n "
                                + "as all k+n*phi with integer k. For u=c+d*phi the output "
                                + "is (c+d)*n+d*k. fiber_output_injective proves that, "
                                + "when d is nonzero, different k always give different "
                                + "outputs. Thus one readout admits an infinite family "
                                + "of distinct one-step outputs on the unrestricted carrier.")),
                        Paragraph(Text(
                            "Selecting floor(n*alpha+rho) fixes one k. A selected "
                                + "invariant section can preserve multiplication within "
                                + "its own image without satisfying this full-fiber "
                                + "criterion. These are different quantified statements."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DescentFormula() => Disp(Call("Iff", Call("Descends", F.Id("u")),
        Seq(Call("b", F.Id("u")), Sp, Eq, Sp, F.Id("0"))));
}
