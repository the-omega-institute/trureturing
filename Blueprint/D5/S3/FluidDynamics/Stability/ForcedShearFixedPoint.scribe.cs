using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Stability;

internal sealed class ForcedShearFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Stability/ForcedShearFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independently proved dissipative comparison controls an actual stationary forced NS shear uniformly over space.",
        H("Stationary forced NS shears and their perturbation tube"),
        Blocks(
            Paragraph(Text("The profile is the predecessor's actual shear (1,k)*cos(-2k*x+2*y), "
                + "with spatial period 2*pi. The field is a(t) times that profile and gamma=4*nu*(k^2+1). "
                + "Ordinary derivatives and the full nsResidual are reused. Pressure is zero. "
                + "Stability is restricted to this invariant family, not arbitrary transverse perturbations.")),
            Entry("field_equation", "An arbitrary amplitude has an explicitly differentiated NS residual",
                "If a has derivative da at t, the actual field has zero divergence and "
                + "NS residual (da+gamma*a(t))*profile.",
                "Reuse the spatial wave derivatives and differentiate the actual amplitude in time. "
                + "The pairing of (1,k) with (-2k,2) vanishes and cancels the full nonlinear advection."),
            Entry("stationary_forced_solution", "A genuine stationary solution for a fixed force",
                "The literal field c*profile solves the NS equation with force gamma*c*profile.",
                "Apply the differential identity to a constant amplitude; the target is constructed explicitly."),
            Entry("amplitude_readout", "The actual velocity contains the amplitude readout",
                "The first velocity component at x=y=0 equals a(t).",
                "Evaluate the original cosine profile, without introducing an auxiliary observation label."),
            Entry("forced_shear_attraction", "Uniform spatial control under bounded forcing error",
                "For nu>0 and a'= -gamma*(a-c)+r with continuous r and abs(r)<=rho, "
                + "the field solves NS with force (gamma*c+r(t))*profile. Every component error is at most "
                + "(1+k)*(exp(-gamma*t)*abs(a(0)-c)+rho/gamma*(1-exp(-gamma*t))).",
                "Derive gamma>0 from the actual frequency, invoke scalar_equilibrium_tube from the "
                + "independently proved DissipativeAttraction module, then bound profile components by 1+k. "
                + "No external proof port remains in this dependency path."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("forced-shear-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
