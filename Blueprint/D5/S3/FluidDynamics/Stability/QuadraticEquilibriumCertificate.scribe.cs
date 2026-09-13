using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Stability;

internal sealed class QuadraticEquilibriumCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Stability/QuadraticEquilibriumCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One independently derived quadratic energy identity controls attraction, stationary uniqueness and residual certification.",
        H("Nonlinear steady-state certificates"),
        Blocks(
            Paragraph(Text("On a real inner product space define the actual vector field F(x)=Lx-B(x,x)+f, "
                + "where L is linear and B is bilinear. Assume inner(b,B(a,b))=0 for every a,b. "
                + "For a fixed reference v, assume inner(w,Lw)<=-mu*norm(w)^2 and "
                + "-inner(w,B(w,v))<=G*norm(w)^2. The positive margin is gamma=mu-G. "
                + "No continuity or boundedness of these algebraic maps is smuggled in; trajectory theorems "
                + "require their own actual derivatives. Continuum NS must first establish its domains and energy identities.")),
            Entry("difference_energy_identity", "The exact remaining interaction about a reference state",
                "inner(w,F(v+w)-F(v))=inner(w,Lw)-inner(w,B(w,v)).",
                "Expand all four bilinear terms and cancel inner(w,B(v,w)) and inner(w,B(w,w)). "
                + "B need not be symmetric. This equality supplies the subsequent energy estimate."),
            Entry("shifted_energy_bound", "A verified negative energy margin",
                "inner(x-v,F(x)-F(v))<=-(mu-G)*norm(x-v)^2 for every x.",
                "Apply the exact difference identity with w=x-v, then combine the linear and strain bounds. "
                + "Contraction of F is a conclusion, rather than the given hypothesis."),
            Entry("residual_controls_state", "An actual residual controls distance to an existing steady state",
                "If F(v)=0 and G<mu, then norm(x-v)<=norm(F(x))/(mu-G).",
                "Use the negative energy inequality and Cauchy-Schwarz. When x differs from v, "
                + "cancel its positive norm; the equality case is handled separately. "
                + "This theorem does not create an equilibrium merely from a small residual."),
            Entry("equilibrium_unique", "A certified steady state excludes every other steady state",
                "Under the same positive margin, F(v)=F(x)=0 implies x=v.",
                "The residual certificate forces norm(x-v)=0. It requires no flow-existence assumption."),
            Entry("nonlinear_equilibrium_tube", "The same margin controls nonlinear trajectories with forcing errors",
                "For u'=F(u)+r with norm(r)<=rho, rho>=0, the error obeys "
                + "norm(u(t)-v)<=exp(-gamma*t)*norm(u(0)-v)+(rho/gamma)*(1-exp(-gamma*t)).",
                "Translate the actual trajectory, use stationary F(v)=0 and the full bilinear cancellation, "
                + "bound the forcing pairing, and invoke independently proved norm_tube_of_energy. "
                + "The result is on the displayed time interval and does not establish global PDE existence."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("quadratic-equilibrium-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
