using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermSecondOrderStructuralResidueDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermSecondOrderStructuralResidue."
            + "golden_germ_second_order_structural_residue";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second-order golden germ has its explicit nonzero structural residue.",
        H("Golden Germ Second-Order Structural Residue"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-second-order-structural-residue"),
            DeclarationHandle.Create(Declaration),
            H("The structural residue is explicit and nonzero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the residue step in the golden Euler germ "
                        + "extraction ladder of OACTC parts 580 and 581. The frozen "
                        + "structural simple-pole theorem fixes the point one over phi "
                        + "cubed and the exact meromorphic order, while this node closes "
                        + "the remaining local boundary by computing the coefficient.")),
                Paragraph(Text(
                    "The residue-one limit for Riemann zeta is transported through "
                        + "multiplication by phi cubed. The other factors are regular at "
                        + "the structural point: the squared zeta argument becomes one "
                        + "over phi, the doubled argument becomes two over phi, and the "
                        + "second normalized product H is continuous there.")),
                Paragraph(Text(
                    "GoldenAuxiliaryZetaNonzero supplies nonvanishing at one over phi. "
                        + "The standard right-half-plane theorem applies at two over phi "
                        + "because one is strictly less than two over phi, and "
                        + "GoldenGermSecondNormalizedFactorRegularity makes H nonzero. "
                        + "Together with the nonzero phi-cubed scale, these facts make "
                        + "the displayed residue nonzero.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: the conclusion concerns only the explicit "
                        + "second-order germ and its punctured neighborhood at one over "
                        + "phi cubed. It does not assert O-5, the Riemann hypothesis, any "
                        + "implication toward either statement, a zero-free region, or "
                        + "any all-orders extraction."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula h = F.Id("H");
        Formula germ = F.Id("F2");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula a = Fraction(F.D(1), phiCubed);
        Formula oneOverPhi = Fraction(F.D(1), F.Varphi);
        Formula twoOverPhi = Fraction(F.D(2), F.Varphi);
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
            Call("F2", s), F.Sp, F.Colon, F.Eq, F.Sp, germAtS);
        Formula residue = F.Seq(
            Call("riemannZeta", oneOverPhi), F.Sp, F.Times, F.Sp,
            Power(F.Seq(F.Open, Call("riemannZeta", twoOverPhi), F.Close),
                F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, Call("H", a),
            F.Sp, F.Slash, F.Sp, phiCubed);
        Formula meromorphic = Call("MeromorphicAt", germ, a);
        Formula simpleOrder = F.Seq(
            Call("meromorphicOrderAt", germ, a),
            F.Sp, F.Eq, F.Sp, F.Minus, F.D(1));
        Formula scaledGerm = F.Seq(
            F.Open, s, F.Sp, F.Minus, F.Sp, a, F.Close,
            F.Sp, F.Times, F.Sp, Call("F2", s));
        Formula residueLimit = Call(
            "Tendsto",
            F.Seq(F.Open, s, F.Colon, F.Sp, ComplexNumbers(), F.Close,
                F.Sp, F.Mapsto, F.Sp, scaledGerm),
            PuncturedNhood(a),
            Call("nhds", residue));
        Formula residueNonzero = F.Seq(
            residue, F.Sp, F.Neq, F.Sp, F.D(0));

        return F.Disp(new Formula.Aligned([
            F.Seq(h, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(hDefinition, F.Comma),
            F.Seq(germ, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(germDefinition, F.Comma),
            F.Seq(F.Id("a"), F.Sp, F.Colon, F.Eq, F.Sp, a, F.Comma),
            F.Seq(meromorphic, F.Sp, F.Land),
            F.Seq(simpleOrder, F.Sp, F.Land),
            F.Seq(residueLimit, F.Sp, F.Land),
            F.Seq(residueNonzero, F.Dot),
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
