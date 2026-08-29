using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermZetaSimplePoleDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole."
            + "golden_germ_zeta_simple_pole";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden germ zeta function has a genuine simple pole at one over phi squared.",
        H("Golden Germ Zeta Simple Pole"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-zeta-simple-pole"),
            DeclarationHandle.Create(Declaration),
            H("The golden germ zeta function has a simple boundary pole"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set a equal to one over phi squared and let G be the normalized "
                        + "prime product. The residue function is the analytic extension "
                        + "of (z-1) zeta(z), evaluated at phi squared times s, multiplied "
                        + "by G(s) over phi squared.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the zeta residue, the removable-singularity "
                        + "extension mechanism, the meromorphic local normal form, and the "
                        + "order criterion. GoldenGermNormalizedFactorRegularity makes G "
                        + "analytic at a, while GoldenGermZetaBoundary makes G(a) nonzero.")),
                Paragraph(Text(
                    "The residue function is therefore analytic and nonzero at a, with "
                        + "value G(a) over phi squared. On the punctured neighborhood, the "
                        + "germ equals (s-a)^(-1) times this residue function. Its "
                        + "meromorphic order is consequently minus one, and the negative "
                        + "order criterion gives convergence to the cobounded filter.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: this theorem closes the boundary singularity "
                        + "question left open by GoldenGermZetaBoundary, using the regularity "
                        + "input supplied by GoldenGermNormalizedFactorRegularity. It says "
                        + "nothing about other points, nothing about the zero set, and "
                        + "nothing about the germ away from the displayed punctured "
                        + "neighborhood."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula germZeta = F.Id("germZeta");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula a = Fraction(F.D(1), phiSquared);
        Formula scaledS = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, LocalFactor(s, p));
        Formula germAtS = F.Seq(
            Call("riemannZeta", scaledS), F.Sp, F.Times, F.Sp,
            PrimeProduct(normalized));
        Formula germDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("germZeta", s), F.Sp, F.Colon, F.Eq, F.Sp, germAtS);
        Formula meromorphic = Call("MeromorphicAt", germZeta, a);
        Formula simpleOrder = F.Seq(
            Call("meromorphicOrderAt", germZeta, a),
            F.Sp, F.Eq, F.Sp, F.Minus, F.D(1));
        Formula punctured = Call(
            "nhdsWithin",
            a,
            F.Seq(
                ComplexNumbers(), F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, a, F.CloseBrace));
        Formula blowsUp = Call(
            "Tendsto",
            germZeta,
            punctured,
            Call("cobounded", ComplexNumbers()));

        return F.Disp(new Formula.Aligned([
            F.Seq(germZeta, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(germDefinition, F.Comma),
            F.Seq(meromorphic, F.Sp, F.Land),
            F.Seq(simpleOrder, F.Sp, F.Land),
            F.Seq(blowsUp, F.Dot),
        ]));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
