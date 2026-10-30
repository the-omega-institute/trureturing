using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class CdsoRareHubProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/CdsoRareHubProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual subset law has a strictly positive CDSO gap of order r to the power three halves.",
        H("A genuine rare extra hub"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cdso-genuine-rare-hub-family"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The complete real-parameter family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a be any integer at least four, r=a+1 and s=a+2. The finite labels " +
                        "are Fin s; adding one to their values identifies them with [s]. The extra " +
                        "label e is the last element and H is its complement, of cardinality a+1. " +
                        "For every real epsilon with 0<epsilon<=1/a, give {e} mass epsilon, H mass " +
                        "(a-1)epsilon, and H with j removed mass (1-a epsilon)/(a+1) for each j in H. " +
                        "Every other subset has mass zero. In particular the empty subset has mass " +
                        "zero, so the array is a probability law on all nonempty subsets.")),
                    Paragraph(Text(
                        "Profile records nonnegativity, total mass one, zero empty mass and positive " +
                        "marginals. Mean, marginal, moment and energy are finite expectations under " +
                        "that single law: q=sum_T x_T |T|, y_i=sum_{T containing i} x_T, " +
                        "w_i=sum_{T containing i} x_T |T|^2, and 2J=sum_i w_i/y_i^2. No independently " +
                        "chosen marginal or relaxed pair law enters these definitions.")),
                    Paragraph(Text(
                        "The mean is a. On H, y_i=(a-epsilon)/(a+1) and " +
                        "w_i=(a^3+epsilon E_a)/(a+1), where E_a=2a^3-2a-1. At the extra label, " +
                        "y_e=w_e=epsilon. Consequently all marginals are positive, including the " +
                        "extra marginal. The original adjacent-cardinality benchmark is " +
                        "F_r(q)=r^2((3(r-1)^2+3(r-1)+1)q-(r-1)r(2r-1))/(2q^2).")),
                    Paragraph(Text(
                        "The exact energy is 2J=(a+1)^2(a^3+epsilon E_a)/(a-epsilon)^2+1/epsilon. " +
                        "Writing A_a=2a^3+2a^2-2a-1, the exact difference is " +
                        "2(J-F_{a+1}(a))=1/epsilon+(a+1)^2 epsilon(A_a-a epsilon)/(a-epsilon)^2. " +
                        "It is strictly positive for every parameter in the stated domain.")),
                    Paragraph(Text(
                        "Support connectivity is the reflexive transitive closure of sharing a " +
                        "positive-mass type. Two labels are connected exactly when either both equal " +
                        "e or neither equals e. H is nonempty and its full type has positive mass; " +
                        "{e} also has positive mass, and no positive-mass type crosses the partition. " +
                        "Thus these are exactly two actual support components. At epsilon=1/a the " +
                        "missing-one masses are zero, while this support conclusion and every " +
                        "positive marginal persist.")),
                    Paragraph(Text(
                        "Put epsilon_a=1/(sqrt(2) a^(3/2)), with the real power and a tending to " +
                        "infinity through natural numbers. This parameter is admissible for every " +
                        "a>=4. Both (J-F_{a+1}(a))/a^(3/2) and " +
                        "(J-F_{a+1}(a))/(a+1)^(3/2) tend to sqrt(2). The difference divided by " +
                        "(a+1)^2 therefore tends to zero. The rational infinite subfamily in the " +
                        "source is a=2b^2, epsilon=1/(4b^3), for integers b>=2; it has the same scale.")),
                    Paragraph(Text(
                        "There is no real c>0 for which J_s(x)-F_r(q)>=c r^2 holds for every " +
                        "integer r>=5, every finite integer s>=r+1, and every actual profile on " +
                        "[s] whose mean belongs to [r-1,r]. Indeed apply such a bound to these " +
                        "profiles with r=a+1, s=a+2 and q=a, and divide by the positive square " +
                        "r^2. The resulting lower bound c contradicts convergence to zero.")),
                    Paragraph(Text(
                        "Finite expectation interchange and the cardinality of an erased finite " +
                        "set compute the masses, mean and moments. Positive support types preserve " +
                        "the core/extra partition along every incidence path; the full core type " +
                        "connects every core pair. Subtracting the native benchmark gives the " +
                        "displayed gap. For the limits, divide by a^(3/2), use its square a^3, " +
                        "and express the quotient through 1/a and epsilon_a/a, both tending to " +
                        "zero. Continuity of division and real powers gives the first limit, " +
                        "and a/(a+1) tending to one gives the second.")),
                    Paragraph(Text(
                        "This is a repository derivation for probability arrays. It asserts neither " +
                        "optimality of this family nor an exact connected graph realization at " +
                        "every finite budget. Its support is disconnected. A prescribed-budget " +
                        "graph realization requires its separate fixed-parameter, capacity and " +
                        "positive-marginal hypotheses. No external literature-priority claim is " +
                        "made for the array construction or its consequences."))),
                DescribeRole.Theorem)),
        []));
}
