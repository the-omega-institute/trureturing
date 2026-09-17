using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class PairedCalibrationDefectIdentifiabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/PairedCalibrationDefectIdentifiability."
            + "uniform_paired_decoder_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicitly weighted pulse-ratio defect gives the sharp condition for "
            + "one decoder of the complete paired record matrix. At the boundary, "
            + "an admissible four-block ensemble collides with a one-block ensemble.",
        H("Sharp Identifiability with Imperfectly Paired Calibration"),
        Blocks(
            Paragraph(Text(
                "Reuse the genuine records(c,g,offset,s,t) of the preceding "
                    + "two-pulse matrix model. In each acquisition block r, two "
                    + "independently prepared copies may have different positive "
                    + "detector gains g and h, different nonnegative offsets, "
                    + "and different positive pulse gains (s,t) and (u,v). "
                    + "For arbitrary finite n and nonnegative exposure weights w "
                    + "with positive total, M_ij is the sum of w times the "
                    + "left record i times the right record j.")),
            Paragraph(Text(
                "Set x=sv and y=ut in each block. Define the actual signal mass "
                    + "S=sum(wgh(x squared+y squared)) and the defect "
                    + "E=sum(wgh(x-y) squared). Admissibility requires "
                    + "E<=eta S, with 0<=eta<1. This is a prior bound on "
                    + "the paired calibration ensemble, not an observable label "
                    + "and not a conclusion stored in a structure. The source "
                    + "derives S>0 from positivity and nonzero exposure.")),
            Describe.Lean(
                DescribeId.Create("uniform-paired-decoder-iff"),
                DeclarationHandle.Create(Declaration),
                H("A complete-matrix decoder exists exactly below the defect boundary"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 0<cLo<cHi, one function from the full 4-by-4 real "
                            + "matrix to Bool labels every admissible ensemble "
                            + "correctly if and only if cLo squared is strictly "
                            + "less than (1-eta)cHi squared. False denotes cLo "
                            + "and true denotes cHi. This quantifies over all "
                            + "deterministic nonlinear matrix decoders and all "
                            + "finite ensemble sizes. It assumes neither an "
                            + "identical detector nor identical pulse magnitudes "
                            + "between the two copies.")),
                    Paragraph(Text(
                        "Let a=(-1,1,0,0), b=(-1,0,1,0), d=(1,-1,-1,1). "
                            + "The source expands actual record products and proves "
                            + "a-transpose M b+b-transpose M a=2S and "
                            + "d-transpose M d=2c squared(S-E). The ratio thus "
                            + "lies in [(1-eta)c squared,c squared]. A fixed "
                            + "midpoint threshold supplies the forward construction "
                            + "without estimating the hidden calibration.")),
                    Paragraph(Text(
                        "For necessity put x=(cHi-cLo)/(cHi+cLo), d=sqrt(x) "
                            + "and a=sqrt(1+x). The high candidate uses "
                            + "calibrations p=(1-d,1+d) and q=(1+d,1-d) "
                            + "paired in the four equally weighted combinations "
                            + "(p,p),(p,q),(q,p),(q,q). The low candidate uses "
                            + "the one pair ((a,a),(a,a)). All detector gains "
                            + "are one and offsets zero. The source proves "
                            + "S=2(1+x) squared, E=8x for the high ensemble, "
                            + "its budget condition, and equality of the entire "
                            + "matrix by an explicit average-record identity. "
                            + "The low ensemble has zero defect. The common "
                            + "matrix cannot receive both correct Bool values.")),
                    Paragraph(Text(
                        "For the previously supplied physical candidates cHi=1 "
                            + "and cLo=1/5, the boundary is eta=24/25. Eta "
                            + "measures a signal-weighted ratio defect and is "
                            + "not a percentage hardware gain tolerance. E=0 "
                            + "requires only matching within-copy pulse ratios "
                            + "on exposed blocks; positive detector gains, offsets "
                            + "and common pulse rescalings may differ.")),
                    Paragraph(Text(
                        "The failure result concerns the full paired second-moment "
                            + "matrix. It is not equality of the complete paired "
                            + "probability laws. The interpretation M_ij=E[X squared "
                            + "Y squared] requires conditional independence, zero "
                            + "means and exogenous setting selection. Gaussian "
                            + "measures, sampling bounds and the later measured-data "
                            + "certificate remain separate ordinary proofs.")),
                    Paragraph(Text(
                        "Grouped latent-variable data and joint state/noise "
                            + "identification are established topics: see "
                            + "Vandermeulen and Scott, arXiv:1502.06644, and "
                            + "Jayakumar et al., Quantum 8, 1426 (2024). "
                            + "This theorem concerns the stated two-candidate "
                            + "control-record family. It does not recover an "
                            + "arbitrary mixture or solve the geometric Fano "
                            + "expectation. Global priority is not asserted."))),
                DescribeRole.Theorem))));

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

    private static Formula Statement() => Disp(Seq(
        Call("OrderedPositiveCandidates", F.Id("cLo"), F.Id("cHi")), Sp, Land, Sp,
        Call("DefectBudgetInUnitInterval", F.Id("eta")), Sp, Rightarrow, Sp,
        new Formula.Relation(
            Call("ExistsOneDecoderForAllPairedMatrices", F.Id("cLo"), F.Id("cHi"), F.Id("eta")),
            FormulaRelationOperator.Equal,
            Call("SharpSquaredCandidateGap", F.Id("cLo"), F.Id("cHi"), F.Id("eta")))));
}
