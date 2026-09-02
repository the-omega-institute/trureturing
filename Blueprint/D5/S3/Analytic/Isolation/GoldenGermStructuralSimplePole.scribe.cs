using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermStructuralSimplePoleDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole."
            + "golden_germ_structural_simple_pole";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second-order golden germ has a genuine simple structural pole.",
        H("Golden Germ Structural Simple Pole"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-structural-simple-pole"),
            DeclarationHandle.Create(Declaration),
            H("The second extracted zeta factor gives a simple pole"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set a equal to one over phi cubed. In the frozen second-order "
                        + "factorization, zeta at phi cubed times s is the pole factor; "
                        + "the product of zeta at phi squared times s, the reciprocal "
                        + "zeta factor at twice phi squared times s, and H is the regular "
                        + "multiplier.")),
                Paragraph(Text(
                    "GoldenGermSecondNormalizedFactorRegularity makes H analytic and "
                        + "nonzero at a. GoldenAuxiliaryZetaNonzero supplies the nonzero "
                        + "value zeta of one over phi, and the standard right-half-plane "
                        + "zeta theorem supplies nonvanishing at two over phi, where the "
                        + "concrete inequality one less than two over phi is verified.")),
                Paragraph(Text(
                    "Transporting the residue-one extension through multiplication by "
                        + "phi cubed yields an analytic nonzero residue. The resulting "
                        + "punctured normal form has exponent minus one, so the germ is "
                        + "meromorphic of exact order minus one and tends to the "
                        + "cobounded filter.")),
                Paragraph(Text(
                    "The real point a is exactly D5.X_Frontier.Hearts.structuralPole by "
                        + "that frontier definition, which is one over phi cubed. The "
                        + "Lean module deliberately uses the numeric point and does not "
                        + "import the open Hearts module.")),
                Paragraph(Text(
                    "Within the golden Euler-germ extraction ladder associated with "
                        + "OACTC parts 580 and 581, this closes the local boundary left by "
                        + "the second extracted zeta factor on the RH-route O-5 control "
                        + "line. It does not prove O-5, does not prove RH, and makes no "
                        + "claim about zeros or other points."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula h = F.Id("H");
        Formula germ = F.Id("F");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula a = Fraction(F.D(1), phiCubed);
        Formula scaledSquared = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula scaledCubed = F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s);
        Formula scaledDouble = F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Times, F.Sp, s);
        Formula secondCancellation = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)),
            F.Close);
        Formula firstNormalizationBase = F.Seq(
            F.Open, F.D(1), F.Sp, F.Plus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close);
        Formula normalizedLocal = F.Seq(
            secondCancellation, F.Sp, F.Times, F.Sp,
            Power(firstNormalizationBase, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, LocalFactor(s, p));
        Formula hDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("H", s), F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(normalizedLocal));
        Formula doubleZetaBase = F.Seq(
            F.Open, Call("riemannZeta", scaledDouble), F.Close);
        Formula germAtS = F.Seq(
            Call("riemannZeta", scaledSquared), F.Sp, F.Times, F.Sp,
            Call("riemannZeta", scaledCubed), F.Sp, F.Times, F.Sp,
            Power(doubleZetaBase, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, Call("H", s));
        Formula germDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("F", s), F.Sp, F.Colon, F.Eq, F.Sp, germAtS);
        Formula meromorphic = Call("MeromorphicAt", germ, a);
        Formula simpleOrder = F.Seq(
            Call("meromorphicOrderAt", germ, a),
            F.Sp, F.Eq, F.Sp, F.Minus, F.D(1));
        Formula punctured = Call(
            "nhdsWithin",
            a,
            F.Seq(
                ComplexNumbers(), F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, a, F.CloseBrace));
        Formula blowsUp = Call(
            "Tendsto",
            germ,
            punctured,
            Call("cobounded", ComplexNumbers()));

        return F.Disp(new Formula.Aligned([
            F.Seq(h, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(hDefinition, F.Comma),
            F.Seq(germ, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
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
