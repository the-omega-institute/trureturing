using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Stability;

internal sealed class ForcedShearFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Stability/ForcedShearFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The OpenAI-derived viscous estimate controls attraction to an actual stationary forced shear, uniformly over space.",
        H("Stationary forced NS shears and their perturbation tube"),
        Blocks(
            Paragraph(Text("The profile is the predecessor's actual shear (1,k)*cos(-2k*x+2*y), "
                + "with spatial period 2*pi. The field is a(t) times that profile, and "
                + "gamma=4*nu*(k^2+1). The same ordinary derivatives and full nsResidual are reused. "
                + "Pressure is zero and forcing is parallel to this profile. All stability statements "
                + "are restricted to this invariant family, not to arbitrary transverse perturbations.")),
            Entry("field_equation", "An arbitrary amplitude has an explicitly differentiated NS residual",
                "If a has derivative da at t, the actual field has zero divergence and "
                + "NS residual (da+gamma*a(t))*profile.",
                "Reuse the predecessor's spatial wave derivatives. Differentiate the actual amplitude "
                + "in time. The velocity direction (1,k) pairs to zero with (-2k,2), "
                + "so the two nonlinear advection terms cancel. The viscous multiplier follows "
                + "from the actual Euclidean second derivatives."),
            Entry("stationary_forced_solution", "A genuine stationary solution for a fixed force",
                "For a(t)=c, the literal field c*profile satisfies the NS equation with the "
                + "time-independent force gamma*c*profile.",
                "Apply the actual differential identity to the constant amplitude. This constructs "
                + "the stationary target instead of assuming an unknown equilibrium exists."),
            Entry("amplitude_readout", "The amplitude is recovered from the actual velocity",
                "The first velocity component at x=y=0 equals a(t).",
                "Evaluate the existing cosine profile at the origin. The amplitude bound "
                + "therefore concerns an actual field coordinate and is not an external label."),
            Entry("forced_shear_attraction", "Uniform spatial control under bounded forcing error",
                "Assume nu>0 and the actual amplitude equation a'= -gamma*(a-c)+r "
                + "on the closed time interval, with continuous r and abs(r)<=rho. "
                + "The field solves the forced NS equation with force (gamma*c+r(t))*profile. "
                + "Every component error is at most (1+k)*(exp(-gamma*t)*abs(a(0)-c) "
                + "+rho/gamma*(1-exp(-gamma*t))), uniformly over x and y.",
                "Prove gamma>0 from nu and the actual frequency. Apply scalar_equilibrium_tube, "
                + "which consumes the OpenAI Hilbert-space estimate. Bound each actual profile "
                + "component by 1+k using abs(cos)<=1. No general NS existence, "
                + "three-dimensional regularity, or nonlinear transverse stability is asserted."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("forced-shear-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
