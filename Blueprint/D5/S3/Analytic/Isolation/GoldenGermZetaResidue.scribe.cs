using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermZetaResidueDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermZetaResidue."
            + "golden_germ_zeta_residue";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simple golden boundary pole has the explicit positive residue G(a) over "
            + "phi squared.",
        H("Golden Germ Zeta Residue"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-zeta-residue"),
            DeclarationHandle.Create(Declaration),
            H("The golden boundary residue is explicit and positive"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the next boundary node in the golden Euler germ "
                        + "extraction ladder of OACTC parts 580 and 581, on the RH-route "
                        + "O-5 control line. The frozen predecessor identifies a genuine "
                        + "simple pole at a equal to one over phi squared; this node closes "
                        + "the remaining explicit-residue boundary by computing its value.")),
                Paragraph(Text(
                    "GoldenGermZetaBoundary supplies the transported limit of the zeta "
                        + "kernel and the exact factorization of (s-a)Z(s). "
                        + "GoldenGermNormalizedFactorRegularity makes G continuous at a, "
                        + "so the product limit is G(a) over phi squared. Frozen real-axis "
                        + "positivity of G(a), together with positivity of phi squared, "
                        + "makes this residue real and strictly positive.")),
                Paragraph(Text(
                    "GoldenGermZetaSimplePole supplies the meromorphic order minus one. "
                        + "STOPPING JUSTIFICATION: the conclusion concerns only the point "
                        + "one over phi squared and its displayed punctured neighborhood. "
                        + "It does not assert O-5, the Riemann hypothesis, any implication "
                        + "toward either claim, a zero-free region, or a pole at any other "
                        + "point."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula g = F.Id("G");
        Formula z = F.Id("Z");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula a = Fraction(F.D(1), phiSquared);
        Formula gAtS = Call("G", s);
        Formula gAtA = Call("G", a);
        Formula zAtS = Call("Z", s);
        Formula scaledS = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, LocalFactor(s, p));
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula zDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            zAtS, F.Sp, F.Colon, F.Eq, F.Sp,
            Call("riemannZeta", scaledS), F.Sp, F.Times, F.Sp, gAtS);
        Formula simpleOrder = F.Seq(
            Call("meromorphicOrderAt", z, a),
            F.Sp, F.Eq, F.Sp, F.Minus, F.D(1));
        Formula residue = F.Seq(gAtA, F.Sp, F.Slash, F.Sp, phiSquared);
        Formula scaledGerm = F.Seq(
            F.Open, s, F.Sp, F.Minus, F.Sp, a, F.Close,
            F.Sp, F.Times, F.Sp, zAtS);
        Formula residueLimit = Call(
            "Tendsto",
            F.Seq(F.Open, s, F.Colon, F.Sp, ComplexNumbers(), F.Close,
                F.Sp, F.Mapsto, F.Sp, scaledGerm),
            PuncturedNhood(a),
            Call("nhds", residue));
        Formula positiveReal = F.Seq(
            Call("Im", residue), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Land, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, F.Re, F.Open, residue, F.Close);

        return F.Disp(new Formula.Aligned([
            F.Seq(g, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(z, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(zDefinition, F.Comma),
            F.Seq(F.Id("a"), F.Sp, F.Colon, F.Eq, F.Sp, a, F.Comma),
            F.Seq(simpleOrder, F.Sp, F.Land),
            F.Seq(residueLimit, F.Sp, F.Land),
            F.Seq(positiveReal, F.Dot),
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

    private static Formula PuncturedNhood(Formula point) =>
        Call(
            "nhdsWithin",
            point,
            F.Seq(
                ComplexNumbers(), F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, point, F.CloseBrace));

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
