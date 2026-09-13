using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Stability;

internal sealed class DissipativeAttractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Stability/DissipativeAttraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent regularized-energy comparison, using mathlib alone, controls actual state errors with a sharp forcing floor.",
        H("Dissipative attraction from regularized energy"),
        Blocks(
            Paragraph(Text("The proof uses z_delta=sqrt(norm(u)^2+delta^2), delta>0. "
                + "No external proof helpers remain. Mathlib provides differentiation and signed scalar Gronwall; "
                + "the regularization inequality and passage to delta=0 are proved in this module.")),
            Entry("norm_tube_of_energy", "An energy-form estimate without a bounded-generator assumption",
                "For a real inner product space H, gamma>0 and rho>=0, let u be continuous on [0,T] "
                + "with actual right derivative du on [0,T). Assume inner(u,du)<=-gamma*norm(u)^2+rho*norm(u). "
                + "Then norm(u(t))<=exp(-gamma*t)*norm(u(0))+(rho/gamma)*(1-exp(-gamma*t)).",
                "Differentiate z_delta using its strictly positive radicand. The inequalities norm(u)<=z_delta "
                + "and delta<=z_delta give z_delta'<=-gamma*z_delta+rho+gamma*delta. "
                + "Apply mathlib scalar Gronwall with its negative coefficient intact and take delta to zero "
                + "by continuity. No norm derivative at zero or trajectory existence premise is concealed. "
                + "The theorem requires a strong Hilbert-space derivative, so it does not automatically apply to weak PDE solutions."),
            Entry("norm_le_exponential_tube", "Actual linear equations instantiate the energy theorem",
                "For u'=A(t)u+f(t), inner(x,A(t)x)<=-gamma*norm(x)^2 and norm(f)<=rho, "
                + "the same sharp norm bound holds for every t in the closed interval.",
                "Prove the required energy inequality using Cauchy-Schwarz and the forcing bound, "
                + "then invoke norm_tube_of_energy. A is a bounded continuous linear map at each time. "
                + "Its continuity in time is not assumed or used; the input trajectory supplies the stated derivative."),
            Entry("unforced_norm_contraction", "Zero forcing retains the negative growth rate",
                "The actual solution of u'=A(t)u under the strict quadratic bound satisfies "
                + "norm(u(t))<=exp(-gamma*t)*norm(u(0)).",
                "Use the energy theorem with rho=0. A finite-interval estimate does not assert global existence."),
            Entry("scalar_equilibrium_tube", "A specified stationary scalar target",
                "For a'=-gamma*(a-c)+r with abs(r)<=rho, the certificate bounds abs(a(t)-c) "
                + "with initial error abs(a(0)-c) and forcing floor rho/gamma.",
                "Translate the actual amplitude to a-c and check the scalar multiplication operator. "
                + "The existing ForcedShearFixedPoint module consumes this result on literal NS fields."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("dissipative-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
