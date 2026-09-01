using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class HalfPlanePositiveKernelCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/TestFunctions/HalfPlanePositiveKernelCriterion."
            + "half_plane_positive_kernel_rh_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Gram positivity packages the half-plane positive-kernel criterion "
            + "for the Riemann hypothesis.",
        H("Half-Plane Positive Kernel Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("half-plane-positive-kernel-rh-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Half-plane positive-kernel RH criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The point type abstracts the half-plane with real part greater than "
                        + "one half. Positive definiteness means that every finite sampled "
                        + "Gram matrix is positive semidefinite, including repeated points.")),
                Paragraph(Text(
                    "The xi-kernel equivalence is retained as an explicit source-criterion "
                        + "hypothesis because the pinned library does not supply the required "
                        + "Hadamard expansion. Independently, the Lean module proves diagonal "
                        + "reality and nonnegativity, conjugate symmetry, the two-point "
                        + "Cauchy-Schwarz bound, and both positive and negative kernel witnesses."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Iff(
        Call("RiemannHypothesis"),
        Call("IsPosDefKernel", F.Id("xiKernel"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
