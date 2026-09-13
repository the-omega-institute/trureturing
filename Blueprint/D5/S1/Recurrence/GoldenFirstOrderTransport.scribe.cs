using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenFirstOrderTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GoldenFirstOrderTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal powers in the existing golden ring transport their p-divisible coefficients "
            + "by an exact first-order identity modulo p squared.",
        H("Golden First-Order Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-coefficient-transport"),
            DeclarationHandle.Create(Prefix + "coefficient_transport"),
            H("Normalized coefficients of equal powers"),
            StatementSource.FromAuthor(Transport()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let p>0, x,y be golden integers, and k,l be natural exponents. "
                    + "Assume x.b=p*a and y.b=p*b in the integers and x^k=y^l. "
                    + "Then k*x.a^(k-1)*a=l*y.a^(l-1)*b in ZMod(p). "
                    + "The exponent equality is an ordinary reusable input to this transport lemma; "
                    + "the Frobenius bridge establishes it using actual powers of phi.")),
                Paragraph(Text("golden_power_first_order proves the exact coefficient formula "
                    + "when the b-coordinate is square-zero. Reduction modulo p squared "
                    + "establishes this condition. cancel_scalar_mod_square cancels p "
                    + "in an integer divisibility witness, never as an invertible "
                    + "element of ZMod(p^2)."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Transport() => Disp(Call("EqMod",
        Call("linearCoefficient", F.Id("x"), F.Id("k"), F.Id("a")),
        Call("linearCoefficient", F.Id("y"), F.Id("l"), F.Id("b")), F.Id("p")));
}
