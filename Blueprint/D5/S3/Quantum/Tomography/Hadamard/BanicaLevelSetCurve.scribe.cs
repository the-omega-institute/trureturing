using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.Hadamard;

internal sealed class BanicaLevelSetCurveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global analytic curves with prescribed directions in regular level sets.",
        H("Curves in regular analytic level sets"),
        Blocks(
            Describe.Lean(DescribeId.Create("globalize-analytic-curve"),
                DeclarationHandle.Create(Prefix + "globalize_analytic_curve"),
                H("Bounded analytic reparametrization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An analytic curve germ through zero with derivative v and satisfying a local property extends to a global analytic curve satisfying that property everywhere, with derivative kappa v for some positive kappa. The scalar substitution r t / sqrt(1+t^2) stays in the germ's interval and has derivative r at zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("analytic-level-set-curve"),
                DeclarationHandle.Create(Prefix + "analytic_level_set_curve"),
                H("Realize every kernel direction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let Phi map finite-dimensional real normed spaces, be globally real analytic, vanish at zero and have surjective derivative there. Every vector v in the derivative kernel is the tangent of a global real analytic curve in the zero level set, up to a positive scalar factor.")),
                    Paragraph(Text("The implicit function is parametrized by the derivative kernel. Its derivative is the kernel inclusion. Restriction to the line spanned by v gives the required curve germ, and the bounded scalar substitution makes the curve global. The regularity constant is the analytic order omega, written as top in ContDiff, which implies smoothness of every finite order."))),
                DescribeRole.Theorem))));
}
