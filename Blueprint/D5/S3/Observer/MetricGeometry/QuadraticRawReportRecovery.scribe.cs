using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class QuadraticRawReportRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic reports retain their original common calibration, joint noise cube and arbitrary deterministic recovery rules.",
        H("Raw Quadratic Report Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-raw-positions"),
                DeclarationHandle.Create(Prefix + "positions"),
                H("The six positions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sampling positions are exactly I={0,1,2,8,9,10}."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-index"),
                DeclarationHandle.Create(Prefix + "Index"),
                H("Original coordinate labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An Index is a natural number in I, retaining its original numerical sampling position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-design"),
                DeclarationHandle.Create(Prefix + "Design"),
                H("Every original report subset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A design J is any finite subset of the original six coordinates, including the empty subset. A design is selected independently of the actual raw reports."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-reports"),
                DeclarationHandle.Create(Prefix + "Reports"),
                H("The complete raw report domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every design J, Reports(J) consists of all real functions on J, including reports incompatible with every legal world."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-prior"),
                DeclarationHandle.Create(Prefix + "prior"),
                H("Known signed prior"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real H and s, prior(H,s) is the closed interval [-5+(s-H)/2,-5+(s+H)/2]. In the clock experiment H>0. Its center is -5+s/2 and its length is H. For positive m and epsilon the normalized noise parameter is c=2*epsilon/m; this normalization does not alter the worlds or the raw noise vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-world"),
                DeclarationHandle.Create(Prefix + "World"),
                H("Finite common calibrations and joint noise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A world consists of real tau, gain and zero, and one function noise from I to the real numbers. Every report in this world shares the same finite gain and zero. Two worlds may choose them independently. No coordinate has its own gain or offset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-legal"),
                DeclarationHandle.Create(Prefix + "Legal"),
                H("The original legal worlds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Legal(m,epsilon,H,s,w) means that w.tau belongs to prior(H,s), w.gain>=m, and |w.noise(i)|<=epsilon for every one of the six original coordinates i. The source experiment assumes m>0, epsilon>0 and H>0. The auxiliary recovery results also include nonnegative epsilon."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-signature"),
                DeclarationHandle.Create(Prefix + "signature"),
                H("Noiseless raw reports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real t,A,B and original coordinate i, signature(t,A,B)(i)=A*(i+t)^2+B. No report difference or coefficient error is substituted for this observation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-observe"),
                DeclarationHandle.Create(Prefix + "observe"),
                H("A projected raw experiment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a design J and a world w, observe(J,w)(i)=w.gain*(i+w.tau)^2+w.zero+w.noise(i) for i in J. The noise vector remains defined and bounded on all six original coordinates. Selecting J only projects that vector and the raw signature."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-rule"),
                DeclarationHandle.Create(Prefix + "Rule"),
                H("Every total deterministic rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every design J, Rule(J) consists of all total functions from Reports(J) to the real numbers. The rule may depend on the known experiment parameters; there is no regularity or computability restriction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-risk"),
                DeclarationHandle.Create(Prefix + "risk"),
                H("Worst-case loss of an arbitrary rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m,epsilon,H,s, design J and total deterministic rule delta, risk is the supremum over all Legal(m,epsilon,H,s,w) of ofReal(|delta(observe(J,w))-w.tau|). This supremum is taken in the extended nonnegative reals, so an individual rule can have infinite risk. There is no measurability, continuity, computability or stochastic-noise restriction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-minimax-risk"),
                DeclarationHandle.Create(Prefix + "minimaxRisk"),
                H("Original deterministic minimax risk"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every parameter tuple and design J, minimaxRisk is the infimum of risk(m,epsilon,H,s,J,delta) over every total deterministic rule delta. Each experiment has its own known H and s. Comparing s=-t and s=t concerns separate known-prior experiments, and does not mix their world sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-compatible"),
                DeclarationHandle.Create(Prefix + "compatible"),
                H("Actual compatible origins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every raw report y on J, compatible(m,epsilon,H,s,J,y) consists of the real t for which some legal original world w has w.tau=t and observe(J,w)=y. This definition neither assumes the fiber is closed nor assumes it is an interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-midpoint-rule"),
                DeclarationHandle.Create(Prefix + "midpointRule"),
                H("A total midpoint rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty compatible set S, midpointRule returns (inf S+sup S)/2. On an empty compatible set it returns the prior center -5+s/2. Thus the rule is defined even at impossible reports. Infimum and supremum do not require the endpoints to belong to S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-pair-compatible"),
                DeclarationHandle.Create(Prefix + "PairCompatible"),
                H("Independent calibrations on the same raw coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real m,epsilon,u,v and design J, PairCompatible means that there exist finite real A,Aprime,B,Bprime with A>=m and Aprime>=m such that |signature(u,A,B)(i)-signature(v,Aprime,Bprime)(i)|<=2*epsilon for every i in J. Both offsets are free, but each remains common to its own world."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-strips"),
                DeclarationHandle.Create(Prefix + "Strips"),
                H("Joint coefficient strips"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real epsilon,U,V and design J, Strips means q(i)-q(j)<=4*epsilon for every ordered pair i,j in J, where q(i)=U*i^2+V*i. These simultaneous inequalities retain the original coordinate correlations. They are not independent bounds on U and V."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-ambiguity-radius"),
                DeclarationHandle.Create(Prefix + "ambiguityRadius"),
                H("A supremum of finite common-world half-gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m,epsilon,H,s,J, ambiguityRadius is the extended nonnegative supremum of ofReal(|u-v|/2) over u and v in prior(H,s) satisfying PairCompatible(m,epsilon,J,u,v). Every member has finite calibrations. The definition makes no claim that a maximizing pair exists, and does not define the minimax risk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-compatible-iff"),
                DeclarationHandle.Create(Prefix + "compatible_iff"),
                H("Projected noise is exactly the original cube projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m,epsilon,H,s with epsilon>=0, every design J, every raw report y on J and every real t, t is compatible with y if and only if t belongs to prior(H,s) and there exist finite real A,B with A>=m and |y(i)-signature(t,A,B)(i)|<=epsilon for every i in J. To extend the projected residuals to a legal original noise vector, use those residuals on J and zero on every unobserved original coordinate. Conversely, an actual world supplies its own common A and B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-common-report-iff"),
                DeclarationHandle.Create(Prefix + "common_report_iff"),
                H("Finite two-world reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m,epsilon,H,s with epsilon>=0, every design J and real u,v, there exist two legal original worlds w,wprime with origins u,v and exactly the same projected raw report if and only if u,v belong to prior(H,s) and PairCompatible(m,epsilon,J,u,v) holds. In the reverse direction the common report is the coordinatewise midpoint of the two noiseless signatures. The two noises on J are opposite half-differences, extended by zero outside J. Both full six-coordinate noise vectors satisfy the original closed cube constraints, and the supplied finite gains and offsets remain common within each world."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-pair-compatible-iff-strips"),
                DeclarationHandle.Create(Prefix + "pairCompatible_iff_strips"),
                H("Exact elimination and reconstruction of one common constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real m,epsilon,u,v and every design J, PairCompatible(m,epsilon,J,u,v) holds if and only if there exist finite A,Aprime>=m such that Strips(epsilon,J,A-Aprime,2*(A*u-Aprime*v)) holds. The forward implication subtracts two bounded coordinate differences. For the reverse implication put U=A-Aprime, V=2*(A*u-Aprime*v), q(i)=U*i^2+V*i and S={q(i):i in J}. When J is nonempty, set C=-(inf S+sup S)/2, B=C-A*u^2+Aprime*v^2 and Bprime=0. The bounded-set midpoint inequality gives |q(i)+C|<=2*epsilon simultaneously at all selected coordinates. The same finite A,Aprime and these two finite offsets then satisfy the original raw bounds. If J is empty no coordinate constraint remains. No independent-coordinate calibration or coefficient-noise cube is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-raw-minimax"),
                DeclarationHandle.Create(Prefix + "raw_minimax"),
                H("Exact raw recovery and a finite attained minimax value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m,epsilon,H,s with epsilon>=0 and every design J, minimaxRisk equals ambiguityRadius. The risk of the total midpointRule equals that same value. Moreover minimaxRisk<=ofReal(H/2) and minimaxRisk is strictly below infinity. These statements apply in particular to all m>0,epsilon>0,H>0 and every signed s in the original experiment. The lower bound tests an arbitrary total rule on each pair of legal finite worlds with one common raw report: one of the two errors is at least half their origin gap. The upper bound applies the bounded-set midpoint inequality to each actual compatible set, which is bounded by the original prior. The argument uses neither closed fibers nor attainment of the supremum of pair gaps. Minimax attainment refers to the midpoint recovery rule, and does not assert an attaining world pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-projection-monotone"),
                DeclarationHandle.Create(Prefix + "projection_monotone"),
                H("Projection cannot improve recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m,epsilon,H,s and every two fixed designs J and K with J contained in K, minimaxRisk(m,epsilon,H,s,K)<=minimaxRisk(m,epsilon,H,s,J). A rule on J is extended to K by discarding the other coordinates of the actual raw report. The original world, common calibration and joint noise vector are the same on both sides."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-raw-few-reports-floor"),
                DeclarationHandle.Create(Prefix + "few_reports_floor"),
                H("At most two reports leave a quarter-width lower floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m>0, epsilon>=0, H>0 and real s, every design J of cardinality at most two has minimaxRisk(m,epsilon,H,s,J)>=ofReal(H/4). To see the finite-world meaning, contain J in a pair {p,q}, allowing p=q. Its response changes sign at k=-(p+q)/2. For every 0<d<H/2, one can place two origins at distance d in the upper or lower half of the prior, strictly on the same side of k. Write M=|u-k|+|v-k| and take A=m*M/|u-k| and Aprime=m*M/|v-k|. These are finite and at least m; their signed responses balance exactly. A single offset difference then makes both raw coordinates identical. Extending zero noise to the remaining original coordinates gives legal finite common worlds. Every rule therefore has risk at least d/2. Taking the supremum as d approaches H/2 gives H/4; no limiting finite endpoint world pair is asserted. Projection transfers this lower bound from the containing pair to J. The bound also covers zero or one report, without identifying their larger exact risks."))),
                DescribeRole.Theorem))));
}
