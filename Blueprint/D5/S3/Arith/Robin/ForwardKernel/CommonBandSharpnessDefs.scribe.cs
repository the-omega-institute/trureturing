using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CommonBandSharpnessDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clipped logarithmic cusps and sparse perturbations for common-band variance sharpness.",
        H("Clipped cusps and sparse perturbations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clipped-log"),
                DeclarationHandle.Create(Prefix + "clippedLog"),
                H("Clipped logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithm of min(k,max(h,abs(y)))/k clips the radial argument between the inner and outer radii."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-jump"),
                DeclarationHandle.Create(Prefix + "logJump"),
                H("Unit logarithmic jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unit logarithmic jump at z is log(abs(z+1))-log(abs(z))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cusp-average"),
                DeclarationHandle.Create(Prefix + "cuspAverage"),
                H("Forward cusp average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cusp average integrates the forward difference of the clipped logarithm at displacement s*q over the unit interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cusp-cross-energy"),
                DeclarationHandle.Create(Prefix + "cuspCrossEnergy"),
                H("Cusp cross energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cusp cross energy integrates over [0,k] the product of the forward cusp averages of lengths h and k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("center"),
                DeclarationHandle.Create(Prefix + "center"),
                H("Geometric spike centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nth spike center is the real number 10^n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplitude"),
                DeclarationHandle.Create(Prefix + "amplitude"),
                H("Spike amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nth amplitude is the square root of X_n*log(X_n)/log(log(X_n)), where X_n=10^n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spike"),
                DeclarationHandle.Create(Prefix + "spike"),
                H("One logarithmic spike"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nth spike is its amplitude times the clipped logarithm with radii X_n^a and X_n^b, translated to center X_n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("admissible-start"),
                DeclarationHandle.Create(Prefix + "AdmissibleStart"),
                H("Separated spike radii"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A starting index n0 is admissible when n0>=1 and X_n^b<=X_n/10 for every n>=n0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("perturbation"),
                DeclarationHandle.Create(Prefix + "perturbation"),
                H("Sparse logarithmic perturbation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The perturbation at x is the sum of the spikes with indices n0+j for natural j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spike-point-scale"),
                DeclarationHandle.Create(Prefix + "spikePointScale"),
                H("Pointwise spike scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pointwise comparison scale is sqrt(x)*log(x)^(3/2)/sqrt(log(log(x)))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("near-opt-scale"),
                DeclarationHandle.Create(Prefix + "nearOptScale"),
                H("Near-optimal cross-energy scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The near-optimal comparison scale is X^(1-b)*log(X)^3/log(log(X))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-log-scale"),
                DeclarationHandle.Create(Prefix + "reducedLogScale"),
                H("Reduced logarithmic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reduced comparison scale is X^(1-b)*log(X)^(3-eta)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative-variance-band-negligible-for"),
                DeclarationHandle.Create(Prefix + "CumulativeVarianceBandNegligibleFor"),
                H("Negligible variance on a band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute normalized variance V_F(Y,u)/(Y*u*log(Y/u)) tends uniformly to zero for Y^alpha<=u<=Y^beta."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "Set clippedLog(h,k,y)=log(min(k,max(h,abs(y)))/k) and "
                + "logJump(z)=log(abs(z+1))-log(abs(z)). The forward cusp average "
                + "cuspAverage(h,k,q,y) integrates clippedLog(h,k,y+s*q)-clippedLog(h,k,y) "
                + "over 0<=s<=1. The cusp cross energy integrates the product of the "
                + "averages at lengths h and k over 0<=y<=k.")),
            Paragraph(Text(
                "The centers are X_n=10^n, the amplitudes are "
                + "A_n=sqrt(X_n*log(X_n)/log(log(X_n))), and the nth spike is "
                + "A_n*clippedLog(X_n^a,X_n^b,x-X_n). An admissible start n0 is at "
                + "least one and satisfies X_n^b<=X_n/10 for every n>=n0. "
                + "The perturbation is the sum of the spikes indexed by n0+j for natural j.")),
            Paragraph(Text(
                "The pointwise scale is sqrt(x)*log(x)^(3/2)/sqrt(log(log(x))). "
                + "The near-optimal cross-energy scale is X^(1-b)*log(X)^3/log(log(X)), "
                + "and the reduced-log comparison scale is X^(1-b)*log(X)^(3-eta). "
                + "Negligible band variance means that the absolute value of "
                + "V_F(Y,u)/(Y*u*log(Y/u)) tends uniformly to zero for Y^alpha<=u<=Y^beta. "
                + "These definitions concern real functions and make no assumption about an arithmetic error.")),
            Describe.Lean(
                DescribeId.Create("center-pos"),
                DeclarationHandle.Create(Prefix + "center_pos"),
                H("Positive centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every center X_n=10^n is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-strict-mono"),
                DeclarationHandle.Create(Prefix + "center_strictMono"),
                H("Increasing centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The map n to X_n=10^n is strictly increasing on the natural numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-tendsto"),
                DeclarationHandle.Create(Prefix + "center_tendsto"),
                H("Centers escape to infinity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sequence X_n tends to positive infinity as n tends to infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-admissible-start"),
                DeclarationHandle.Create(Prefix + "exists_admissibleStart"),
                H("An admissible starting index exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real b<1 there exists n0>=1 such that "
                    + "X_n^b<=X_n/10 for every n>=n0. Indeed, X_n^(b-1) tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clipped-log-eq-zero"),
                DeclarationHandle.Create(Prefix + "clippedLog_eq_zero"),
                H("Vanishing beyond the outer radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If k>0 and abs(y)>=k, then clippedLog(h,k,y)=0, for every real h."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-support-subset"),
                DeclarationHandle.Create(Prefix + "spike_support_subset"),
                H("Outer support bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all real a and b and every natural n, the support of the nth spike "
                    + "is contained in [X_n-X_n^b,X_n+X_n^b]. Outside this interval "
                    + "the clipped logarithm equals log(1)=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-intervals-disjoint"),
                DeclarationHandle.Create(Prefix + "spike_intervals_disjoint"),
                H("Strict separation of outer intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an admissible start, if i<j, then the right endpoint of the "
                    + "outer interval at index n0+i is strictly less than the left "
                    + "endpoint at index n0+j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-locally-finite"),
                DeclarationHandle.Create(Prefix + "spike_locallyFinite"),
                H("Locally finite spike supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an admissible start, the supports of the spikes indexed by n0+j "
                    + "form a locally finite family. Each support has left endpoint at least "
                    + "nine tenths of its center, and these lower bounds tend to infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-finite-support"),
                DeclarationHandle.Create(Prefix + "perturbation_finite_support"),
                H("Finite support in the summation index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an admissible start and at each fixed real x, only finitely many "
                    + "spikes in the perturbation are nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-locally-single-spike"),
                DeclarationHandle.Create(Prefix + "perturbation_locally_single_spike"),
                H("A single possible spike on a neighbourhood"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an admissible start, every real point has a neighbourhood U such "
                    + "that any two spikes nonzero anywhere in U have the same index. "
                    + "The closed outer support intervals are locally finite and pairwise "
                    + "disjoint: their radii are at most one tenth of their centers and "
                    + "successive centers differ by a factor of ten."))),
                DescribeRole.Theorem))));
}
