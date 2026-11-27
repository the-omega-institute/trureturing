using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class PhaseResummationLogGermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The imaginary part of the resummed phase has an exact cubic logarithmic germ at zero coupling.",
        H("The logarithmic germ of the resummed phase"),
        Blocks(
            Paragraph(Text("The sine series can be integrated after geometric damping. Removing the damping gives the sine-log integral. "
                + "The bound on log(sin(t)/t) controls the remainder. The singular term g³log|g| gives the divergent slope of the second derivative.")),
            Definition("phase-resummed-function", "F", "Resummed phase",
                "For each real g, F(g) is the sum of the radial mode terms at g."),
            Definition("phase-clausen-function", "clausen2", "Clausen sine series",
                "Clausen2(θ) is the sum over positive integers n of sin(nθ)/n²."),
            Definition("phase-cubic-germ", "cubicGerm", "Cubic logarithmic term",
                "The two-sided cubic logarithmic term is g³(log(2|g|) − 1)."),
            Result("phase-imaginary-clausen", "phase_im_eq_neg_clausen", "Imaginary part as a sine series",
                "For every real g, Im F(g) = −(g²/2) Clausen2(2g)."),
            Result("phase-real-bernoulli", "phase_re_eq_bernoulli", "Real part on the principal interval",
                "For |g| ≤ π, Re F(g) = π²g²/12 − π|g|³/2 + g⁴/2."),
            Result("phase-imaginary-integral", "phase_im_eq_integral", "Logarithmic integral",
                "For 0 ≤ g ≤ π, Im F(g) equals g² times the integral from 0 to g of log(2 sin t)."),
            Result("phase-imaginary-cubic-bound", "phase_im_cubic_bound", "Explicit fifth-order error",
                "For |g| ≤ 1, the absolute difference between Im F(g) and the cubic logarithmic term is at most |g|⁵/15."),
            Result("phase-imaginary-right-germ", "phase_im_right_germ", "Exact right-hand germ",
                "As g approaches zero from above, Im F(g) = −g³ log(1/g) + (log 2 − 1)g³ + O(g⁵)."),
            Result("phase-first-derivative-zero", "phase_hasDerivAt_zero", "First derivative at zero",
                "The real derivative of the complex-valued resummed phase at zero is zero."),
            Result("phase-second-derivative-zero", "phase_deriv_hasDerivAt_zero", "Derivative of the first derivative",
                "The first derivative of the resummed phase has real derivative π²/6 at zero, viewed as a complex number."),
            Result("phase-second-iterated-derivative-zero", "phase_iteratedDeriv_two_zero", "Second iterated derivative at zero",
                "The second iterated real derivative of F at zero is π²/6, viewed as a complex number."),
            Result("phase-twice-continuously-differentiable-interval", "phase_contDiffOn_two", "Twice continuous differentiability",
                "The resummed phase is twice continuously differentiable on the open interval (−π, π)."),
            Result("phase-twice-continuously-differentiable-zero", "phase_contDiffAt_two", "Twice continuous differentiability at zero",
                "The resummed phase is twice continuously differentiable at zero."),
            Result("phase-imaginary-third-derivative-obstruction", "phase_im_second_not_differentiable", "Imaginary third derivative obstruction",
                "The second iterated derivative of the imaginary part is not differentiable at zero."),
            Result("phase-third-derivative-obstruction", "phase_second_no_hasDerivAt", "Complex third derivative obstruction",
                "No complex number is a derivative of the twice differentiated resummed phase at zero."))));

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullCone),
            Blocks(Paragraph(Text(statement))), DescribeRole.Definition);

    private static DocumentBlock Result(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullCone),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
