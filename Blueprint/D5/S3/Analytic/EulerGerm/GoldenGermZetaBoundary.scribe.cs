using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermZetaBoundaryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary."
            + "golden_germ_zeta_boundary_reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the golden germ convergence boundary, the formal data isolate regularity of "
            + "the normalized factor as a sufficient missing input.",
        H("Golden Germ Zeta Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-zeta-boundary-reduction"),
            DeclarationHandle.Create(Declaration),
            H("Boundary data isolate regularity as a sufficient missing input"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The point one over phi squared lies strictly to the right of one over "
                        + "phi cubed, so it is inside the continued half-plane. The exact "
                        + "identity isolates the transported zeta residue from G. The frozen "
                        + "real-ray positivity also holds at the boundary itself.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the punctured limit of (z-1) times zeta(z) "
                        + "at z=1. Multiplication by phi squared transports that limit to "
                        + "s=1/phi squared. Restriction to the real ray, frozen factorization, "
                        + "and positive real-ray nonvanishing give the divided-factor limit. "
                        + "The complex punctured source filter is explicitly non-bottom.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: the complex-neighborhood conclusion remains "
                        + "Rung 1 and does not establish that the abscissa is a genuine "
                        + "singularity. The divided-factor limit is the real-axis analogue of "
                        + "Rung 2, but pointwise positivity does not prevent G from tending to "
                        + "zero along that ray. Complex Rung 2 needs G nonzero on a punctured "
                        + "complex neighborhood. Continuity of G at one over phi squared is a "
                        + "sufficient future input for Rung 3; it is not asserted here, and the "
                        + "frozen cancellation majorants needed for it are private.")),
                Paragraph(Text(
                    "Downward, direct projections and standard equivalences from this "
                        + "conjunction are corollaries without distinct declarations because "
                        + "no consumer, independent semantics, dependency barrier, or "
                        + "substantial proof content was demonstrated. Upward, continuity or "
                        + "complex-neighborhood nonvanishing crosses the identified dependency "
                        + "barrier and has substantial analytic proof content, so it warrants "
                        + "a distinct future regularity contract."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula continuation = F.Id("Zqc");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdCubed = Fraction(F.D(1), Power(F.Varphi, F.D(3)));
        Formula a = thresholdSquared;
        Formula gAtS = Call("G", s);
        Formula gAtA = Call("G", a);
        Formula gAtSigma = Call("G", sigma);
        Formula scaledS = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula zetaScaled = Call("riemannZeta", scaledS);
        Formula local = LocalFactor(s, p);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, local);
        Formula domain = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.CloseBrace);
        Formula domainHypothesis = F.Seq(
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close);
        Formula computation = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            domainHypothesis, F.Sp, F.Rightarrow, F.Sp,
            Call("Zqc", s), F.Sp, F.Eq, F.Sp,
            zetaScaled, F.Sp, F.Times, F.Sp, gAtS);
        Formula identity = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            domainHypothesis, F.Sp, F.Rightarrow, F.Sp,
            F.Open, s, F.Sp, F.Minus, F.Sp, a, F.Close,
            F.Sp, F.Times, F.Sp, Call("Zqc", s), F.Sp, F.Eq, F.Sp,
            F.Open,
            F.Open, scaledS, F.Sp, F.Minus, F.Sp, F.D(1), F.Close,
            F.Sp, F.Times, F.Sp, zetaScaled,
            F.Close, F.Sp, F.Times, F.Sp,
            F.Open, gAtS, F.Sp, F.Slash, F.Sp, phiSquared, F.Close);
        Formula residueKernel = F.Seq(
            F.Open, scaledS, F.Sp, F.Minus, F.Sp, F.D(1), F.Close,
            F.Sp, F.Times, F.Sp, zetaScaled);
        Formula puncturedAtA = PuncturedNhood(a);
        Formula transportedResidue = Call(
            "Tendsto",
            F.Seq(F.Open, s, F.Colon, F.Sp, ComplexNumbers(), F.Close,
                F.Sp, F.Mapsto, F.Sp, residueKernel),
            puncturedAtA,
            Call("nhds", F.D(1)));
        Formula nonVacuity = Call("NeBot", puncturedAtA);
        Formula boundaryPositivity = F.Seq(
            F.D(0), F.Sp, F.Lt, F.Sp, F.Re, F.Open, gAtA, F.Close,
            F.Sp, F.Land, F.Sp,
            Call("Im", gAtA), F.Sp, F.Eq, F.Sp, F.D(0));
        Formula realGermProduct = PrimeProduct(LocalFactor(sigma, p));
        Formula dividedRealProduct = F.Seq(
            F.Open,
            F.Open, sigma, F.Sp, F.Minus, F.Sp, a, F.Close,
            F.Sp, F.Times, F.Sp, realGermProduct,
            F.Close, F.Sp, F.Slash, F.Sp, gAtSigma);
        Formula realDividedLimit = Call(
            "Tendsto",
            F.Seq(F.Open, sigma, F.Colon, F.Sp, RealNumbers(), F.Close,
                F.Sp, F.Mapsto, F.Sp, dividedRealProduct),
            RightNhood(a),
            Call("nhds", Fraction(F.D(1), phiSquared)));

        return F.Disp(new Formula.Aligned([
            F.Seq(F.Id("G"), F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
                gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized), F.Comma),
            F.Seq(F.Exists, F.Sp, continuation, F.Colon, F.Sp, domain, F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(F.Open, computation, F.Close, F.Sp, F.Land),
            F.Seq(thresholdCubed, F.Sp, F.Lt, F.Sp, thresholdSquared, F.Sp, F.Land),
            F.Seq(F.Open, boundaryPositivity, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, identity, F.Close, F.Sp, F.Land),
            F.Seq(transportedResidue, F.Sp, F.Land),
            F.Seq(realDividedLimit, F.Sp, F.Land, F.Sp, nonVacuity, F.Dot),
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

    private static Formula RightNhood(Formula point) =>
        Call("nhdsWithin", point, Call("Ioi", point));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

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
