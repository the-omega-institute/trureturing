using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class RandomKernelExtremumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp overlap estimates and fixed stochastic approximation to independence.",
        H("Random label replacement and independence completion"),
        Blocks(
            Paragraph(Text(
                "For a natural dimension d, put c(d,k)=(k-1)/(k(d+k-2)), "
                + "beta(d)=max of c(d,k) over 0<=k<=d, and rho(d)=(d-1)beta(d). "
                + "Real division is used, including division by zero equal to zero. "
                + "The indices zero and one contribute zero. For d>=2 this agrees "
                + "with the maximum over 2<=k<=d. Define g(b,a,x)="
                + "(1-x)min(b,x)+x min(a,x).")),
            Describe.Lean(
                DescribeId.Create("sharp-simplex-overlap-bound"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelExtremum.sharp_simplex_overlap_bound"),
                H("All three pieces of the overlap function"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d>=2 and every nonnegative real vector s on Fin d "
                    + "whose coordinates sum to one, 1-rho(d)<=sum_i "
                    + "g(beta(d),1-rho(d),s(i)). No scalar bound is an additional hypothesis.")),
                    Paragraph(Text(
                    "Write b=beta(d) and a=1-rho(d). Adjacent comparisons at a "
                    + "maximizing support size give a^2<=4b. If any coordinate is at "
                    + "least a, it supplies an extra b above the linear lower bound "
                    + "(a-b)s(i). Otherwise split the coordinates at b. Cauchy-Schwarz "
                    + "on the middle coordinates reduces the assertion to the support "
                    + "inequalities defining beta; zero and one middle coordinate are "
                    + "handled separately."))), DescribeRole.Theorem),
            Paragraph(Text(
                "Let T(i,x) equal 1-rho(d) for x=i and beta(d) otherwise. For an active "
                + "joint table p, firstOutput(p)(x,y)=sum_i p(i,y)T(i,x). The active "
                + "kernel optimalActive is the average of firstOutput(p) and the "
                + "corresponding operation changing only the second coordinate.")),
            Describe.Lean(
                DescribeId.Create("active-joint-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelExtremum.active_joint_upper_bound"),
                H("Arbitrary active joint laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every d>=2 and every nonnegative real joint table p on "
                    + "Fin d times Fin d with total mass one, the total variation "
                    + "between optimalActive(p) and the product of the two marginals "
                    + "is at most rho(d). Total variation is half the finite L1 sum. "
                    + "Finite triangle inequalities bound the first-coordinate channel "
                    + "by sum_i u(i)TV(T(i),u), which is exactly one minus the "
                    + "simplex overlap sum. Joint convexity combines the two channels."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The full source space is Option(Fin d times Fin d); none is the "
                + "blocking state. Put Z=p(none) and r=1-Z. Completion retains Z and "
                + "assigns u(i)v(j)/r to each active pair when r>0, and zero active "
                + "mass when r=0. The output-first matrix optimalKernel fixes none "
                + "and acts on active inputs by the average of the two T channels. "
                + "Its diagonal probability is 1-rho(d); changing exactly one "
                + "coordinate to a specified other label has probability beta(d)/2. "
                + "Thus the probability of changing each coordinate is rho(d)/2.")),
            Describe.Lean(
                DescribeId.Create("optimal-kernel-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelExtremum.optimal_kernel_upper_bound"),
                H("The fixed stochastic kernel for all blocked sources"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every d>=2, every matrix entry of optimalKernel is nonnegative "
                    + "and each column sums to one. For every nonnegative normalized "
                    + "source p on the full source space, TV(optimalKernel*p,completion(p)) "
                    + "is at most rho(d). For r>0, normalization of the active table "
                    + "gives the stronger bound r*rho(d). When r=0 every active entry "
                    + "is zero and both output laws coincide at the blocking vertex."))),
                DescribeRole.Theorem))));
}
