using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenCell5040SmallPrimeExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power residue excludes every additional prime below forty seven.",
        H("Small Prime Exclusion For The 5040 Residue"),
        Blocks(
            Paragraph(Text("Let the natural index be divisible by 5040 and satisfy the power "
                + "congruence with residue 2241. The earlier exponent-window theorem fixes the "
                + "old primes two, three, five and seven. Here every prime strictly between "
                + "seven and forty seven is excluded from the index. This is a statement "
                + "about all indices satisfying the two hypotheses, with no bound on the index.")),
            Paragraph(Text("The proof first exposes the reusable kernel "
                + "modEq_period_not_dvd: a period-one residue at a divisor contradicts a "
                + "distinct target residue whenever the period divides the exponent. The "
                + "5040 theorem consumes this kernel for each explicit small-prime period.")),
            Describe.Lean(
                DescribeId.Create("cell-5040-small-prime-not-dvd"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion.modEq_2241_small_prime_not_dvd"),
                H("No residual prime below forty seven"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Sp, F.Id("p"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(5,0,4,0), Sp, Mid, Sp, F.Id("n"), Sp, Land, Sp,
                    new Formula.Power(D(3), F.Id("n")), Sp, Equiv, Sp, D(2,2,4,1), Sp,
                    Open, Mathrm, Grp(F.Id("mod")), Sp, F.Id("n"), Close, Sp, Land, Sp,
                    Call("Prime", F.Id("p")), Sp, Land, Sp,
                    D(7), Sp, Lt, Sp, F.Id("p"), Sp, Lt, Sp, D(4,7), Sp,
                    Implies, Sp, Neg, Grp(Seq(F.Id("p"), Sp, Mid, Sp, F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The possible primes are eleven, thirteen, seventeen, "
                        + "nineteen, twenty three, twenty nine, thirty one, thirty seven, "
                        + "forty one and forty three. For all except twenty three, explicit "
                        + "periods 5, 3, 16, 18, 28, 30, 18, 8 and 42 respectively divide "
                        + "5040. Raising a period-one congruence to the symbolic quotient "
                        + "forces residue one, contradicting the residue of 2241.")),
                    Paragraph(Text("Twenty three needs a different argument. Three has "
                        + "eleventh power one modulo twenty three, so any power of three has "
                        + "eleventh power one there. The eleventh power of 2241 instead has "
                        + "residue twenty two. This case uses only the power congruence.")),
                    Paragraph(Text("The scalar periods and residue contradictions are checked "
                        + "by Lean kernel computation; the exponent of the original index is "
                        + "handled symbolically. The result does not bound the number of "
                        + "residual prime factors, exclude forty seven, or prove the Robin "
                        + "inequality or the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
