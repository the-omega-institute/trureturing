using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class QuadraticMidpointEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximal incomplete quadratic energy has logarithmic average size over its quadratic coefficient.",
        H("Quadratic Energy with Arbitrary Linear Twists"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-maximal-energy-average"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/QuadraticMidpointEnergy.quadratic_maximal_energy_average_le"),
                H("Average the quadratic coefficient after differencing"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a prime greater than two and let Z be a natural number smaller than p. "
                        + "For each a modulo p, quadraticMaximalEnergy is the supremum of the squared norm of "
                        + "the sum of e_p(a(m+j)^2) w^j over 0 <= j < n, where m is any residue, "
                        + "w is any complex number of norm one and 0 <= n <= Z. The theorem bounds the sum "
                        + "of these suprema by p Z (5 + 2 log p). In particular, the interval and the linear "
                        + "twist can be chosen independently for each quadratic coefficient. The case Z=0 is included.")),
                    Paragraph(Text(
                        "The proof expands the squared norm into its diagonal and fixed-lag correlations. "
                        + "Each correlation factors into a unit constant and a geometric progression with ratio e_p(2ah). "
                        + "Its norm is at most the smaller of Z and 2 divided by the chord length from e_p(2ah) to one; "
                        + "the resonant value is Z. The chord lower bound follows from Jordan's sine inequality. "
                        + "A residue and its negative together bound the average majorant by Z + p H_(p-1). "
                        + "For every lag 1 <= h <= Z, multiplication by 2h permutes the residue field. "
                        + "Summing the uniform majorant therefore gives p Z (3 + 2 H_(p-1)), and the harmonic-number "
                        + "logarithmic bound gives the displayed constant. Taking the supremum uses the same "
                        + "majorant and requires no interchange of a supremum and a finite average.")),
                    Paragraph(Text(
                        "This is a project proof of a classical finite differencing estimate, with no literature novelty claim. "
                        + "It supplies the quadratic-energy step used in Theorem 12.1 of the Pascadi physical-plane "
                        + "midpoint argument. The analytic plane-weight variation bound, stationary-phase formula, "
                        + "root multiplicity and summation over plane normals are separate arguments and are not "
                        + "conclusions of this module. Integer interval origins reduce modulo p; a constant unit factor "
                        + "from translating a linear twist does not affect the squared norm."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement() => Disp(F.Seq(
        Forall, Sp, F.Id("p"), Comma, Sp, F.Id("Z"), Colon, Sp, F.Id("N"), Comma, Sp,
        Call("Prime", F.Id("p")), Comma, Sp, D(2), Lt, F.Id("p"), Comma, Sp,
        F.Id("Z"), Lt, F.Id("p"), Sp, Implies, Sp,
        Sum, Underscore, Grp(F.Id("a"), InMacro, Call("ZMod", F.Id("p"))), Sp,
        Call("quadraticMaximalEnergy", F.Id("p"), F.Id("Z"), F.Id("a")), Leq, Sp,
        F.Id("p"), Sp, F.Id("Z"), Open, D(5), Plus, D(2), Call("log", F.Id("p")), Close));
}
