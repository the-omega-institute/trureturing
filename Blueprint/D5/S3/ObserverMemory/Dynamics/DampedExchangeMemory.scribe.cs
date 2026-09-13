using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class DampedExchangeMemoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/Dynamics/DampedExchangeMemory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual resolved-hidden ODE yields state-energy decay, a signed memory equation and a conditioned state readout.",
        H("Dissipative exchange, memory and observation"),
        Blocks(
            Paragraph(Text("Use the literal system x'=-a*x+b*y and y'=-b*x-d*y. Its energy is x^2+y^2. "
                + "The kernel K(t)=-b^2*exp(-d*t), the convolution and the initial-state term are constructed "
                + "and identified from that same ODE. This finite model is not declared to equal an arbitrary NS truncation.")),
            Entry("exchange_energy_identity", "Skew exchange cancels in the full state energy",
                "2*x*resolvedRhs+2*y*hiddenRhs=-2*a*x^2-2*d*y^2 for all real parameters and states.",
                "Expand the actual two right-hand sides. The terms involving b cancel exactly."),
            Entry("state_energy_decay", "Actual state energy decays independently of coupling strength",
                "If a,d>=gamma>0 and both coordinates solve the stated ODE, then "
                + "E(t)<=E(0)*exp(-2*gamma*t) throughout the given closed time interval.",
                "Differentiate x^2+y^2, use the cancellation identity and apply mathlib signed scalar Gronwall. "
                + "The trajectories must exist on the interval; existence is not supplied by this inequality."),
            Entry("memoryTerm_factored", "A genuine signed Volterra convolution",
                "The integral from zero to t of K(t-s)*x(s) equals -b^2*exp(-d*t) "
                + "times the integral of exp(d*s)*x(s).",
                "Use the exponential addition law inside the actual integral and factor out its constant multiplier."),
            Entry("hidden_history_formula", "Hidden-state elimination is derived from its ODE",
                "For continuous x and an actual differentiable hidden solution on [0,t], "
                + "y(t)=exp(-d*t)*(y(0)-b*integral(exp(d*s)*x(s))).",
                "Differentiate exp(d*t)*y(t). Its derivative is -b*exp(d*t)*x(t). "
                + "Apply the fundamental theorem of calculus and multiply by exp(-d*t)."),
            Entry("resolved_memory_equation", "The actual resolved derivative includes hidden initialization",
                "x'(t)=-a*x(t)+b*exp(-d*t)*y(0)+integral(K(t-s)*x(s)).",
                "Substitute the proved hidden-history formula into the original resolved derivative "
                + "and identify the actual convolution. The hidden initial-state term is retained."),
            Entry("hidden_restart_error", "A controlled finite-memory initialization error",
                "For the same prescribed resolved input x, two hidden solutions with d>0 satisfy "
                + "abs(b*(y(t)-z(t)))<=abs(b)*exp(-d*t)*abs(y(0)-z(0)).",
                "Subtract their actual equations and consume the independently proved scalar contraction. "
                + "This is a same-input restart bound. Closing the perturbed resolved feedback is a separate estimate."),
            Entry("exact_jet_recovery", "Visible state and rate identify hidden state when b is nonzero",
                "recoverHidden(a,b,x,resolvedRhs(a,b,x,y))=y for b!=0.",
                "The reconstruction is the explicit quotient (observedRate+a*observedState)/b."),
            Entry("noisy_jet_recovery", "The reconstruction carries an explicit conditioning cost",
                "State error at most epsilon_x and rate error at most epsilon_v give hidden error "
                + "at most (epsilon_v+abs(a)*epsilon_x)/abs(b), for b!=0.",
                "Subtract the exact reconstruction, combine the two actual observation errors and apply the triangle inequality. "
                + "No uniform reconstruction bound as b tends to zero is inferred from state stability."),
            Entry("stationary_hidden_elimination", "The static correction is the same coupling and damping",
                "If hiddenRhs=0 and d!=0, then y=-b*x/d and resolvedRhs=-(a+b^2/d)*x.",
                "Solve the actual hidden stationary equation and substitute it. "
                + "This is the scalar Schur complement of the same two-state system."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("damped-memory-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
