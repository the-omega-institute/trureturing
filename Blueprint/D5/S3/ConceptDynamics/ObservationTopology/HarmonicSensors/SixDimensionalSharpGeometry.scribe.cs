using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors;

internal sealed class SixDimensionalSharpGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp physical chord gains and rank-defect limits for the six-coordinate paired sensor.",
        H("Physical correlation on a rescaled moving domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sixdimensionalsharpgeometry-actual-eta-scaled-limit"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_eta_scaled_limit"),
                H("The sharp normalized correlation maximum"),
                StatementSource.FromAuthor(ActualEtaLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For epsilon>0, let Z=9+20epsilon and take the paired frequencies 2, 3 and 4 "
                        + "with amplitudes sqrt(epsilon)/sqrt(Z), 1/sqrt(Z), and sqrt(epsilon)/sqrt(Z). "
                        + "The sensor has the real cosine and sine coordinate pair for each frequency. "
                        + "Its two-delay matrix has rows given by the sensor at phi and at phi-pi/6. "
                        + "For two distinct physical circle states, form the difference of these matrices. "
                        + "The quantity actualRank(epsilon) is the infimum of its Frobenius-norm square "
                        + "divided by its Euclidean operator-norm square over every such pair of states. "
                        + "Define actualEta(epsilon)=2/actualRank(epsilon)-1.")),
                    Paragraph(Text(
                        "In the statement, Tendsto is convergence of a real-valued function between "
                        + "filters, nhds is the neighborhood filter on the real line, and "
                        + "nhdsWithin(0,Ioi(0)) is the neighborhood filter of zero within (0,infinity). "
                        + "Thus the limit is taken as epsilon tends to zero through strictly positive "
                        + "real values, and its value is exactly 1/(2sqrt(2)).")),
                    Paragraph(Text(
                        "For 0<epsilon<=1/2, the row Gram matrix has diagonal entries E and "
                        + "off-diagonal entries C, where E is the common row energy and C is the "
                        + "row correlation. Its eigenvalues are E+C and E-C. Hence the Frobenius-norm "
                        + "square is 2E and the operator-norm square is E+|C|. With "
                        + "q=4cos((phi-psi)/2)^2-1, the absolute correlation ratio is "
                        + "Q(epsilon,q)=(epsilon/2)|q(q+1)(2-q)|/[q^2(1+epsilon(q-1))+2epsilon]. "
                        + "On this same range 0<epsilon<=1/2, actualEta(epsilon) is the maximum "
                        + "of Q(epsilon,q) over -1<=q<=3, and actualRank(epsilon)=2/(1+max Q). "
                        + "Every -1<=q<3 is realized by a pair of distinct physical circle states; "
                        + "q=3 is approached by short chords.")),
                    Paragraph(Text(
                        "Put t=sqrt(epsilon) and q=tz. The normalized quotient Q(epsilon,tz)/t "
                        + "equals S(t,z)=|z(1+tz)(2-tz)|/[2(z^2(1+t^2(tz-1))+2)]. "
                        + "The limiting profile is L(z)=|z|/(z^2+2). If t>=0, R>=0, |z|<=R, "
                        + "tR<=1 and t^2<=1/4, then |S(t,z)-L(z)| is at most "
                        + "(tR^2+t^2R^3)/4+R^3t^2(1+tR)/4. For fixed R this bound tends to "
                        + "zero as t tends to zero, giving uniform convergence on bounded intervals.")),
                    Paragraph(Text(
                        "The rescaled physical domain is -1/t<=z<=3/t. If 0<epsilon<=1/4, "
                        + "R>0 and |z|>=R within this domain, the normalized quotient is at most 4/R. "
                        + "Taking R=32 makes this tail bound 1/8, strictly below the maximum "
                        + "1/(2sqrt(2)) of L. The point z=sqrt(2) attains that limiting maximum "
                        + "and belongs to the rescaled domain for all sufficiently small positive "
                        + "epsilon. The bounded-interval estimate and tail bound give the upper "
                        + "limit bound, while this realized point gives the lower limit bound.")),
                    Paragraph(Text(
                        "The definitions chordGain, gainValues, lowerGain and upperGain use the "
                        + "actual sensor chord divided by the Euclidean chord of circleState, with "
                        + "all pairs of distinct physical states included. The identity chord_gain_sq "
                        + "gives chordGain^2=P(epsilon,q)/Z, where "
                        + "P(epsilon,q)=q^2(1+epsilon(q-1))+2epsilon. For "
                        + "0<epsilon<=1/2 and -1<=q<=3, the coefficient "
                        + "1+epsilon(q-1) is nonnegative, so P>=2epsilon. The value q=0 is "
                        + "realized by a third-turn chord and attains equality. Taking the infimum "
                        + "therefore gives lowerGain^2=2epsilon/(9+20epsilon).")),
                    Paragraph(Text(
                        "On the same parameter range, q^2<=9 and "
                        + "1+epsilon(q-1)<=1+2epsilon give P<=9+20epsilon. Thus every physical "
                        + "chord gain is at most one. Differentiating each cosine-sine pair gives "
                        + "squared speed sum_i a_i^2 k_i^2=(4epsilon+9+16epsilon)/Z=1 "
                        + "at every phase. The physical circle also has unit speed. The quotient "
                        + "of their short-chord lengths tends to one, proving that the supremum "
                        + "upperGain equals one. This derivative and supremum calculation is an "
                        + "application of the coordinate derivative and one-sided slope-limit laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixdimensionalsharpgeometry-rank-defect-lower-gain-limit"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_rank_defect_lower_gain_limit"),
                H("Rank defect relative to the least physical chord gain"),
                StatementSource.FromAuthor(RankDefectGainLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here actualRank retains the infimum of the actual two-delay Frobenius "
                        + "norm squared divided by the actual Euclidean operator norm squared, "
                        + "at the fixed delay pi/6. The lowerGain in the denominator is the "
                        + "infimum of the sensor-to-circle chord norm ratio over all distinct "
                        + "physical state pairs. The limit is through strictly positive epsilon.")),
                    Paragraph(Text(
                        "The correlation maximum characterization gives "
                        + "2-actualRank=2actualEta/(1+actualEta) for 0<epsilon<=1/2. "
                        + "The established actual_eta_scaled_limit and sqrt(epsilon)->0 imply "
                        + "actualEta->0. Using sqrt(epsilon/2)=sqrt(epsilon)/sqrt(2), "
                        + "actual_rank_defect_scaled_limit gives "
                        + "(2-actualRank)/sqrt(epsilon/2)->1. The sharp lower gain formula "
                        + "gives lowerGain/sqrt(epsilon)=sqrt(2/(9+20epsilon)), "
                        + "which tends to sqrt(2)/3. Dividing these limits and the constant "
                        + "sqrt(2) yields the stated value 3/2.")),
                    Paragraph(Text(
                        "The minimum of three frequency pairs and nonattainment of rank two "
                        + "for every finite injective harmonic family are separate assertions. "
                        + "Neither assertion follows from this fixed six-coordinate family "
                        + "and its small-epsilon asymptotics."))),
                DescribeRole.Theorem))));

    private static Formula ActualEtaLimitFormula() => Disp(Call("Tendsto",
        Seq(Open, Varepsilon, Colon, Sp, Mathbb, Grp(F.Id("R")), Close,
            Sp, Mapsto, Sp, Frac, Grp(Call("actualEta", Varepsilon)),
            Grp(Sqrt, Grp(Varepsilon))),
        Call("nhdsWithin", Num(0), Call("Ioi", Num(0))),
        Call("nhds", Seq(Frac, Grp(Num(1)),
            Grp(Num(2), Sp, Cdot, Sp, Sqrt, Grp(Num(2)))))));

    private static Formula RankDefectGainLimitFormula() => Disp(Call("Tendsto",
        Seq(Open, Varepsilon, Colon, Sp, Mathbb, Grp(F.Id("R")), Close,
            Sp, Mapsto, Sp, Frac,
            Grp(Num(2), Sp, Minus, Sp, Call("actualRank", Varepsilon)),
            Grp(Call("lowerGain", Varepsilon))),
        Call("nhdsWithin", Num(0), Call("Ioi", Num(0))),
        Call("nhds", Seq(Frac, Grp(Num(3)), Grp(Num(2))))));

}
