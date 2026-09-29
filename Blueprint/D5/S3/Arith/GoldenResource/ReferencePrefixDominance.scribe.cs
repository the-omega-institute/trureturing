using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ReferencePrefixDominanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite geometric-prefix logarithm is strictly below its harmonic prefix.",
        H("Strict Finite Prefix Dominance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-geometric-prefix-strict-harmonic-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/GoldenResource/ReferencePrefixDominance."
                    + "log_geom_prefix_lt_harmonic_prefix"),
                H("Strict finite prefix comparison"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exponent a is any natural number at least one, "
                        + "and z is any real number strictly between zero and one. Both "
                        + "sums are finite. The proof differentiates their difference and "
                        + "uses the strict bound on the geometric sum to obtain a positive "
                        + "derivative; its value at zero is zero.")),
                    Paragraph(Text("For z = 1/p this gives the strict prime-axis prefix "
                        + "clause of the Robin reference comparison. The theorem does not "
                        + "include reference maximization, a uniform signed-tail estimate, "
                        + "the Robin inequality or the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = F.Id("a");
        Formula z = F.Id("z");
        Formula k = F.Id("k");
        Formula geometric = Seq(Sum, Underscore, Grp(Seq(k, Eq, D(0))),
            Caret, Grp(a), Sp, new Formula.Power(z, k));
        Formula harmonic = Seq(Sum, Underscore, Grp(Seq(k, Eq, D(1))),
            Caret, Grp(a), Sp, new Formula.Fraction(new Formula.Power(z, k), k));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, z, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Sp, a, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma),
            Seq(D(1), Sp, Le, Sp, a, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, z, Sp, Land, Sp, z, Sp, Lt, Sp, D(1),
                Sp, Rightarrow),
            Seq(new Formula.Apply(F.Id("log"), [geometric]), Sp, Lt, Sp, harmonic)
        ]));
    }
}
