using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenModReturnBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GoldenModReturnBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The existing GoldenMod algebra works at arbitrary composite and prime-power "
                + "moduli. Its faithful matrix action identifies the golden-unit order "
                + "with the already established Fibonacci sequence period.",
            H("Golden Residue Algebra and Return Period"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-mod-order-period"),
                    DeclarationHandle.Create(Prefix + "period_eq_golden_order"),
                    H("The two existing objects have exactly the same order"),
                    StatementSource.FromAuthor(OrderFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural modulus q, regularRepresentation sends "
                                + "a+b*phi to [[a+b,b],[b,a]] over ZMod(q). "
                                + "regularRepresentation_mulVec proves that this is "
                                + "actual multiplication on the coordinate vector (b,a). "
                                + "The map is an injective ring homomorphism, and it "
                                + "sends GoldenMod.phi to the existing Fibonacci companion.")),
                        Paragraph(Text(
                            "The source imports GoldenApparition.GoldenMod and its "
                                + "reduce map rather than creating a new quadratic algebra. "
                                + "period_dvd_iff_reduced_phi connects every return time "
                                + "to reduction of the original GoldenInt power phi^t. "
                                + "The statements do not require primality or discard "
                                + "ramified moduli.")),
                        Paragraph(Text(
                            "Together with period_dvd_iff_sequence, this closes the "
                                + "potential factor-of-two ambiguity between the actual "
                                + "sequence period, companion order, and golden-unit order. "
                                + "It does not turn an ordinary finite-modulus identity "
                                + "into a claim about a real golden-rotation period."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula OrderFormula() => Disp(Seq(
        Call("period", F.Id("q")), Sp, Eq, Sp,
        Call("orderOf", Call("goldenUnitMod", F.Id("q")))));
}
