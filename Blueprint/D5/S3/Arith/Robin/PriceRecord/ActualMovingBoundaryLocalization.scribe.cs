using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualMovingBoundaryLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform moving-index actual boundary localization.",
        H("One-sided exchanges at the original full record"),
        Blocks(
            Paragraph(Text("FullRecord ranges over every positive integer below the same original m, at its arbitrary original positive mu. The comparison price is literally beta(1,largestPrime(m)). No recordhood at that price, own clock, global optimizer, nonnegative epsilon or unsigned fee is assumed.")),
            Paragraph(Text("The real-center short-interval count supplier gives a constant B before delta and one threshold T before m, mu and every j in 2<=j<=delta*log(P)/(log(log(P)))^2+1. With its width C, take H=1024*(1+C) and B=H+16*C. The conclusion is active literal cutoff, positive actual layerPrime and logarithmic error at most B*P^(-priceExponent j). The separately typed maximum-gap premise is retained and unused. This result is conditional on the stated analytic suppliers. Typed Reg actual laws, exact source bridges and observational dependence are partial audit evidence; lawful source-bound four-slot registration and whole-family law sensitivity remain unfinished under issue 29429.")),
            Describe.Lean(
                DescribeId.Create("actual-moving-displaced-root-boundary-squeeze"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.displaced_root_boundary_squeeze"),
                H("displaced_root_boundary_squeeze"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two strict one-sided exchanges constrain the boundary without assuming exact probe valuations. Above Q_j the insertion marginal dominates beta_j; below Q_j the deletion marginal is dominated by beta_j. Strict greedy subsets preserve exact mass ties and the original signed term -mu*(positive mass gap). The integrated lower logarithmic slope excludes the two probe pools separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-counted-displaced-root-boundary-squeeze"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.counted_displaced_root_boundary_squeeze"),
                H("counted_displaced_root_boundary_squeeze"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal real-center short-interval count law is applied at P, rm and rp. The first upper closed interval is erased at its natural endpoint P; the two probe intervals stay closed. Equal finite cardinalities and logarithmic endpoints supply the mass comparisons and disjointness. The first-layer Lipschitz bound is used only at index 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-counted-displaced-cutoff-log-localization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.counted_displaced_cutoff_log_localization"),
                H("counted_displaced_cutoff_log_localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root is the active cutoff at literal beta(1,P). At rm=rho*exp(-H*t) and rp=rho*exp(H*t), t=P^(-priceExponent j), the finite scalar conditions yield positive actual layerPrime and logarithmic error at most (H+16*C)*t. The constant contains no j. The finite count capacities, root activation, root geometry and smallness inequalities are explicit premises; this theorem does not establish one eventual threshold for growing j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-literal-root-geometry"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.literal_root_geometry"),
                H("literal_root_geometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At beta(j,rho)=beta(1,P), uniform geometric beta bounds give P*log(P)/2<=rho^j*log(rho)<=2*P*log(P). Taking logarithms gives log(P)-log(2)<=j*log(rho)<=5*log(P)/4 under the displayed scalar logarithmic condition. The literal first-layer price is never identified with referencePrice(P)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-literal-cutoff-active"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.literal_cutoff_active"),
                H("literal_cutoff_active"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For log(P)>=4 and 2<=j<=log(P)/4, compare the first-layer beta upper bound to the uniform beta lower bound at 2. This proves beta(1,P)<beta(j,2) simultaneously in the full index range and activates the clamped root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-literal-displaced-probe-geometry"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.literal_displaced_probe_geometry"),
                H("literal_displaced_probe_geometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put t=P^(-priceExponent j), rm=rho*exp(-H*t) and rp=rho*exp(H*t). When H*t<=1, the literal root bounds give log(rm)>=log(P)/j-2, log(rp)>=log(P)/j-1 and log(rp)<=5*log(P)/(4*j)+1. Both relative BHP widths r^theta/r are at most 4*t, with no exponential dependence on j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-window-log-scale"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.moving_window_log_scale"),
                H("moving_window_log_scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive delta and A, eventually every positive real u<=delta*x/(log x)^2+1 satisfies A*log(x)<=x/u. The exact identity L*log(x)/x=delta/log(x)+log(x)/x tends to zero. The threshold precedes u, so this is a simultaneous moving-window assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-window-exp-small"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.moving_window_exp_small"),
                H("moving_window_exp_small"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive delta,a and every natural k, eventually x^k*exp(-a*x/u)<=1/x simultaneously over all positive u in the moving window. Apply the preceding logarithmic scale with A=(k+1)/a and exponentiate. No fixed-index asymptotic or finite set of indices is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-uniform-moving-boundary-localization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.bhp_uniform_moving_boundary_localization"),
                H("bhp_uniform_moving_boundary_localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the separately typed native BHPMaximumGap and BHPShortIntervalCount. There exists B>0 such that for every delta>0 there exists T>0 before all m>=2, original mu>0, FullRecord(m,mu), P=largestPrime(m)>=T and all natural 2<=j<=delta*log(P)/(log(log(P)))^2+1: cutoff(j,beta(1,P))>2, layerPrime(m,j)>0 and |log(layerPrime(m,j))-log(cutoff(j,beta(1,P)))|<=B*P^(-priceExponent j).")),
                    Paragraph(Text("Choose K=comparisonCount(j,P), e=48*C*P^(-priceExponent 1), q=8*j/K and Z=log(P)/(4*j). Uniform window decay controls H*j*t, hence all finite smallness conditions. The first count capacity follows from x*exp(-23*x/80)->0; both displaced-root capacities follow uniformly from z*exp(-z/20)->0 with z=x/j. Literal root geometry supplies center thresholds, strict pool separation and mass endpoints. These facts discharge every scalar premise of counted_displaced_cutoff_log_localization on its live proof path. B=1024*(1+C)+16*C depends only on the count supplier width. No recordhood at lambda, price-sign assumption, exact probe valuation or growing-index use of fixed-layer limits occurs."))),
                DescribeRole.Theorem)
        )));
}
