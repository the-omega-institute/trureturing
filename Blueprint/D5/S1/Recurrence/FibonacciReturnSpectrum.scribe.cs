using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciReturnSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciReturnSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The existing Lucas matrix order equals the period of the entire Fibonacci "
                + "sequence. Its return moduli are exactly the divisors of an executable integer.",
            H("Fibonacci Return Spectrum"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("return-spectrum-duality"),
                    DeclarationHandle.Create(Prefix + "period_dvd_iff_dvd_returnContent"),
                    H("Return times and observation moduli satisfy divisibility duality"),
                    StatementSource.FromAuthor(Duality()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For all natural q,t, G(t)=gcd(F(t),F(t+1)-1). "
                                + "period(q) is the existing LucasCompanion.matrixPeriod "
                                + "at parameters 1 and -1 over ZMod(q). "
                                + "fibUnit_power and period_dvd_iff_sequence prove the "
                                + "connection to actual Fibonacci values at every index; "
                                + "the sequence/matrix period equality is not assumed.")),
                        Paragraph(Text(
                            "Time zero has G(0)=0 and admits every positive modulus. "
                                + "Modulus one has period one. The Lean statement also "
                                + "retains ZMod(0)'s integer-ring convention; positivity "
                                + "is claimed only for positive finite moduli."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("return-spectrum-gcd"),
                    DeclarationHandle.Create(Prefix + "returnContent_gcd"),
                    H("The actual return content is a strong divisibility sequence"),
                    StatementSource.FromAuthor(GcdFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For all natural s,t, G(gcd(s,t))=gcd(G(s),G(t)). "
                                + "The companion period_lcm theorem proves "
                                + "period(lcm(a,b))=lcm(period(a),period(b)), without "
                                + "a coprimality premise. Both follow from the exact "
                                + "duality by divisibility antisymmetry.")),
                        Paragraph(Text(
                            "square_period_eq_iff specializes this same return spectrum "
                                + "to the Wall-Sun-Sun plateau condition. It is a criterion, "
                                + "not an existence or nonexistence result for exceptional primes."))),
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

    private static Formula Duality() => Disp(Call("Iff",
        Call("divides", Call("period", F.Id("q")), F.Id("t")),
        Call("divides", F.Id("q"), Call("G", F.Id("t")))));

    private static Formula GcdFormula() => Disp(Seq(
        Call("G", Call("gcd", F.Id("s"), F.Id("t"))), Sp, Eq, Sp,
        Call("gcd", Call("G", F.Id("s")), Call("G", F.Id("t")))));
}
