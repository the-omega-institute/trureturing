using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Stability;

internal sealed class OpenAIViscousAttractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Stability/OpenAIViscousAttraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An OpenAI-source viscous norm argument gives an exact exponential attraction tube with nonzero initial error and bounded forcing.",
        H("OpenAI viscous estimates for stable equilibria"),
        Blocks(
            Paragraph(Text("The three private Hilbert-space helpers are adapted from OpenAI's "
                + "NavierStokes/ViscousPropagator.lean at f9e8bc5b38b6e212696e8a30e3e91517af887bbd, "
                + "under Apache-2.0. Their right-derivative and closed-interval continuity assumptions are retained. "
                + "They are consumed by the public estimates below; no upstream terminal theorem is postulated as an axiom.")),
            Entry("norm_le_exponential_tube", "A bounded forcing produces a quantified attraction tube",
                "For the actual Hilbert-space equation u'=A(t)u+f(t), assume "
                + "inner(x,A(t)x)<=-gamma*norm(x)^2 with gamma>0, and norm(f(t))<=rho. "
                + "The conclusion is norm(u(t))<=exp(-gamma*t)*norm(u(0)) "
                + "+rho/gamma*(1-exp(-gamma*t)). The norm is the actual state norm.",
                "Use the upstream weighted norm argument with W(t)=exp(-gamma*t). "
                + "Bound its forcing integral by the integral of rho*exp(gamma*t), "
                + "evaluate that integral by an explicit antiderivative, and multiply by W. "
                + "The proof retains the exact time and initial data. It assumes the displayed solution "
                + "on its interval, and does not prove global existence for arbitrary NS data."),
            Entry("unforced_norm_contraction", "Zero forcing gives actual norm contraction",
                "With the same strict operator bound and f=0, norm(u(t)) is bounded by "
                + "exp(-gamma*t)*norm(u(0)) on the whole closed interval.",
                "Apply the preceding bound at rho=0. This conclusion keeps the negative growth sign; "
                + "a uniqueness estimate with positive growth does not supply this contraction. "
                + "For a globally existing solution with a common gamma, this estimate implies attraction to zero."),
            Entry("scalar_equilibrium_tube", "A stationary target is included by translating the actual trajectory",
                "For an actual scalar amplitude a'= -gamma*(a-c)+r, with abs(r)<=rho, "
                + "the same estimate bounds abs(a(t)-c) using abs(a(0)-c).",
                "Translate to the actual error a-c. The continuous linear map is multiplication "
                + "by -gamma, whose quadratic-form bound is proved exactly. "
                + "ForcedShearFixedPoint consumes this result on a literal periodic NS field."))));

    private static DocumentBlock.Describe Entry(string name, string title, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("oai-viscous-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}
