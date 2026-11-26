using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicShortTimeWeightDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicShortTimeWeight";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short lifted frequencies incur a quadratic deficit from the spatial majorant.",
        H("Fourier weight in a short range of cyclic frequencies"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-short-frequency-deficit"),
            DeclarationHandle.Create(Owner + ".low_fourier_weight_deficit"),
            H("A quadratic deduction from the zero-mode budget"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The modulus q is a positive integer and F is a nonnegative real function " +
                    "on the residue classes. The finite sets R and J contain integers. " +
                    "Reduction modulo q is injective on R. For a real a, require " +
                    "F(r mod q) ≥ a for r in R and 2 |rk| ≤ q for every r in R and k in J. " +
                    "The transform uses the negative character. Repeated residues represented " +
                    "in J contribute once for each representative.")),
                Paragraph(Text(
                    "Subtract each selected real Fourier coefficient from the zero coefficient. " +
                    "The difference is a sum of F(x) times the character deficit at x. " +
                    "Keep the terms from R. On each pair from R and J, 2 |rk| ≤ q puts the " +
                    "angle in the principal interval. The cosine inequality on that interval " +
                    "bounds its deficit below by 8 r² k² / q². The two sums of squares " +
                    "factor because the bound holds on the full product of the two sets.")),
                Paragraph(Text(
                    "If the Fourier coefficients are nonnegative real and F(0)>0, divide " +
                    "by q F(0) to read their masses as a probability distribution. If J also " +
                    "has distinct residues, this bounds its probability mass and hence the " +
                    "weight left for frequencies outside J. These hypotheses apply to the " +
                    "cyclic prefix-pair kernel. An arithmetic bound on the remaining zero " +
                    "harmonics is a separate input."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var r = F.Id("r");
        var k = F.Id("k");
        var a = F.Id("a");
        var x = F.Id("x");
        var f = F.Id("F");
        var rSet = F.Id("R");
        var jSet = F.Id("J");
        Formula Over(Formula variable, Formula domain) =>
            new Formula.Subscript(Sum, Seq(variable, Sp, InMacro, Sp, domain));
        var transform = new Formula.Apply(Seq(Widehat, Grp(f)), [k]);
        var residues = Seq(Mathbb, Grp(F.Id("Z")), Slash, q, Mathbb, Grp(F.Id("Z")));
        return Disp(new Formula.Aligned([
            Seq(Amp, Over(k, jSet), Sp, Re, Sp, transform, Plus,
                new Formula.Fraction(Seq(D(8), a), new Formula.Power(q, D(2))), Sp,
                Open, Over(r, rSet), Sp, new Formula.Power(r, D(2)), Close, Sp,
                Open, Over(k, jSet), Sp, new Formula.Power(k, D(2)), Close),
            Seq(Amp, Sp, Le, Sp, Bar, jSet, Bar, Sp, Over(x, residues), Sp, Call("F", x), Dot)
        ]));
    }
}
