using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class SecondOrderInterfaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance band gives uniform weighted second moments and the second mixed-moment interface.",
        H("The second-order dyadic interface"),
        Blocks(
            Paragraph(Text(
                "Let E be a locally bounded Borel measurable real function and assume 0<alpha<theta<beta<1 "
                + "and the uniform cumulative variance asymptotic (490.2). These conditional second-order results "
                + "supply no arithmetic proof for E=psi-id and no higher-order interfaces.")),
            Describe.Lean(
                DescribeId.Create("explicit-second-moment-bound"),
                DeclarationHandle.Create(Prefix + "explicit_second_moment_bound"),
                H("An explicit second moment bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "For all sufficiently large X and every s in [0,1], the dyadic probability integral of "
                        + "|B_X(s)|^2 is at most 1760/log(2). The macroscopic lengths a(u)=s*u^theta have size at most "
                        + "two and derivative at most one. The uniform bound 880*M with M=2, followed by logarithmic "
                        + "probability normalization, gives the stated constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-modulus"),
                DeclarationHandle.Create(Prefix + "time_modulus"),
                H("A uniform time modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "For every 0<delta<=1 and eta>0, eventually in X and uniformly for s,t in [0,1] with "
                        + "|s-t|<=delta, the dyadic probability integral of (B_X(s)-B_X(t))^2 is at most "
                        + "120*delta/log(2)+eta. Apply the local moving-endpoint estimate to x+s*x^theta and x+t*x^theta, "
                        + "with R=2*delta*X^theta, derivative lower bound one and enclosing interval [X,2*X+2*X^theta]. "
                        + "The variance-window error and X^theta/X vanish before any time parameters are chosen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-covariance-uniform"),
                DeclarationHandle.Create(Prefix + "weighted_covariance_uniform"),
                H("Uniform weighted Brownian covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "For each continuous real phi on [1,2], the covariance of phi(U_X)*B_X(s)*B_X(t) converges "
                        + "uniformly over (s,t) in [0,1]^2 to kappa*min(s,t) times the integral of phi(u)/u on [1,2], "
                        + "divided by log(2). The macroscopic covariance theorem gives each fixed pair after replacing "
                        + "the local logarithm by log(X); the explicit second moment bound controls that replacement. The "
                        + "time modulus bounds covariance changes by Young's inequality. A finite net in the compact "
                        + "parameter square upgrades the fixed-pair limits to the uniform limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-moment-interface"),
                DeclarationHandle.Create(Prefix + "second_moment_interface"),
                H("The second mixed-moment interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "The variance band implies MomentInterface at order two, with kernel "
                        + "kappa*dyadicMacroMoment(kappa)*min(s(0),s(1)). Choose phi(u)=u^kappa in the weighted "
                        + "covariance limit. The two-factor product and dyadic scaling exponent are exactly those in "
                        + "dyadicMixedMoment. The coefficient is the second-order dyadic power moment, distinct from the "
                        + "fourth-order moment constant."))),
                DescribeRole.Theorem))));
}
