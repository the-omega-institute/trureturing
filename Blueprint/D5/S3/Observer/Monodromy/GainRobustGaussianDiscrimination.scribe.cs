using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class GainRobustGaussianDiscriminationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Monodromy/GainRobustGaussianDiscrimination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A specified two-pulse experiment has a sharp unknown-gain collision boundary. "
            + "Adding reference settings gives one calibration-independent decision "
            + "certificate with a measured-data error radius.",
        H("Unknown-Gain Discrimination and Reference Measurements"),
        Blocks(
            Paragraph(Text(
                "Use the actual dualPulse matrices from TwoPulseCovarianceTomography. "
                    + "The four readout coordinates are q1, p1, p1+q2, p1+p2. "
                    + "The pairing matrix and real symmetric covariance C(c) are explicit "
                    + "in the Lean source. Acting with pulse 1 of strength s and pulse 3 "
                    + "of strength t in dual order gives the actual coefficient vector "
                    + "(1,s,0,t). Matrix contraction derives the variance "
                    + "v_c(s,t)=1+s^2+2cst+2t^2. The corresponding state controls "
                    + "have reverse order. Physical Gaussian inputs are supplied by "
                    + "the companion theory at c=1 and c=1/5. Other c are algebraic "
                    + "parameters; physicality is not implicitly asserted.")),
            Describe.Lean(
                DescribeId.Create("sharp-gain-interval-dichotomy"),
                DeclarationHandle.Create(Prefix + "sharp_gain_interval_dichotomy"),
                H("A sharp universal threshold and explicit coincident experiments"),
                StatementSource.FromAuthor(Dichotomy()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume 0<=cLo<cHi and 0<=delta<1. Both actual gains range "
                            + "independently over [1-delta,1+delta]. One real threshold "
                            + "lies strictly above every v_cLo and below every v_cHi "
                            + "if and only if (3+2cLo)(1+delta)^2 "
                            + "<(3+2cHi)(1-delta)^2. When this condition fails, "
                            + "the source constructs two allowed calibration pairs "
                            + "with exactly equal actual output variances.")),
                    Paragraph(Text(
                        "The extrema are derived from the matrix variance, using "
                            + "positive gains and the nonnegative mixed coefficient. "
                            + "In the separated case their midpoint is a single "
                            + "threshold that does not depend on the unknown gains. "
                            + "For the collision, choose both high-hypothesis gains "
                            + "equal to l=1-delta and both low-hypothesis gains equal "
                            + "to l sqrt((3+2cHi)/(3+2cLo)). The failed strict "
                            + "separation inequality proves the latter gains lie "
                            + "inside the same allowed box. Thus failure is "
                            + "witnessed by actual parameters, not just missing proof.")),
                    Paragraph(Text(
                        "For the physical pair cHi=1,cLo=1/5, the boundary is "
                            + "delta=(5-sqrt(17))/(5+sqrt(17)). Equal zero-mean "
                            + "Gaussian variances imply equal one-setting homodyne "
                            + "laws. The statistical no-go and finite-shot optimal "
                            + "threshold are ordinary consequences, not probability "
                            + "theorems exported by this Lean source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("certified-reference-discrimination"),
                DeclarationHandle.Create(Prefix + "certified_reference_discrimination"),
                H("One observed-data certificate removes unknown stable calibration"),
                StatementSource.FromAuthor(ReferenceDecision()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For common unknown positive variance gain g, common additive "
                            + "variance offset b and nonzero s,t, the four records are "
                            + "b+g times the actual variances of empty, first-pulse, "
                            + "second-pulse and both-pulse experiments. From measured "
                            + "records z define a=z1-z0, b0=z2-z0, d=z3-z1-z2+z0 "
                            + "and F=d^2-a b0. The decision radius is "
                            + "R=(8|d|+2|a|+2|b0|)epsilon+20epsilon^2.")),
                    Paragraph(Text(
                        "Assume c=1 or c=1/5, every record is within epsilon>=0 "
                            + "of its actual value, and |F|>R. Then either "
                            + "c=1 and F>0, or c=1/5 and F<0. The rule uses "
                            + "only measured records and their error certificate, "
                            + "with no calibration-dependent classifier chosen later.")),
                    Paragraph(Text(
                        "Actual matrix readback yields F_ideal="
                            + "2(2c^2-1)(gst)^2. The four-record differences have "
                            + "errors 2epsilon,2epsilon,4epsilon. A proved product "
                            + "perturbation inequality, applied to the squared "
                            + "contrast and the two reference differences, gives "
                            + "|F_ideal-F|<=R. Strict separation of the measured "
                            + "score interval then proves the input classification.")),
                    Paragraph(Text(
                        "The certificate may abstain. Uniform finite-shot power "
                            + "requires signal and noise bounds; arbitrarily small "
                            + "gains or arbitrarily large detector noise cannot have "
                            + "a common finite sample guarantee. Gains and the "
                            + "variance offset must be shared by the reference settings. "
                            + "The source does not model setting-dependent drift, "
                            + "arbitrary non-Gaussian input, unknown couplings, or "
                            + "a universal entanglement witness beyond these two inputs."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "General Gaussian tomography and testing with nuisance parameters "
                    + "are established topics. The explicit control-restricted "
                    + "collision and reference-assisted certificate are the scope "
                    + "here. No global novelty or solved geometric monodromy "
                    + "conjecture is claimed. Gaussian physicality, separability, "
                    + "Chernoff bounds and finite-shot risk are independently "
                    + "explained ordinary mathematics, not hidden Lean assumptions.")))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Dichotomy() => Disp(Seq(
        Forall, Sp, F.Id("cLo"), Comma, Sp, F.Id("cHi"), Comma, Sp, F.Id("delta"),
        Comma, Sp, Call("OrderedNonnegativeCoefficients", F.Id("cLo"), F.Id("cHi")),
        Sp, Land, Sp, Call("GainRadiusInZeroOne", F.Id("delta")), Sp, Rightarrow, Sp, Open,
        new Formula.Relation(
            Call("UniformStrictThreshold", F.Id("cLo"), F.Id("cHi"), F.Id("delta")),
            FormulaRelationOperator.Equal,
            Call("StrictEndpointGap", F.Id("cLo"), F.Id("cHi"), F.Id("delta"))),
        Sp, Land, Sp, Open,
        Call("EndpointOverlap", F.Id("cLo"), F.Id("cHi"), F.Id("delta")),
        Sp, Rightarrow, Sp,
        Call("ExistsAllowedEqualVarianceGains", F.Id("cLo"), F.Id("cHi"), F.Id("delta")), Close, Close));

    private static Formula ReferenceDecision() => Disp(Seq(
        Forall, Sp, F.Id("c"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("b"), Comma, Sp,
        F.Id("s"), Comma, Sp, F.Id("t"), Comma, Sp, F.Id("epsilon"), Comma, Sp,
        F.Id("z"), Comma, Sp,
        Call("OneOrOneFifth", F.Id("c")), Sp, Land, Sp, Call("Positive", F.Id("g")),
        Sp, Land, Sp, Call("NonzeroGains", F.Id("s"), F.Id("t")), Sp, Land, Sp,
        Call("Nonnegative", F.Id("epsilon")), Sp, Land, Sp,
        Call("RecordErrorsWithin", F.Id("z"), F.Id("c"), F.Id("g"), F.Id("b"),
            F.Id("s"), F.Id("t"), F.Id("epsilon")), Sp, Land, Sp,
        Call("AbsoluteScoreExceedsRadius", F.Id("z"), F.Id("epsilon")),
        Sp, Rightarrow, Sp, Call("CorrectSignedDecision", F.Id("c"), F.Id("z"))));
}
