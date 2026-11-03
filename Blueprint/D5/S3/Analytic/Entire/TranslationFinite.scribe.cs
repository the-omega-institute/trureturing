using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class TranslationFiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differentiation preserves finite translation spaces.",
        H("Differentiation preserves finite translation spaces"),
        Blocks(Describe.Lean(DescribeId.Create("finite-entire-translation-derivative"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/TranslationFinite.deriv_mem_of_finite_translation_invariant"),
            H("Differentiation preserves finite translation spaces"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite-dimensional complex submodule W of all functions Complex -> Complex, if translation by every complex number preserves W, then the scalar derivative of each entire member of W also lies in W. The topology is pointwise convergence on the whole complex plane. No completed Fock differentiation operator or boundedness of differentiation in the Fock norm is assumed.")),
                Paragraph(Text("For each nonzero t, t inverse times (f(.+t)-f) is an actual member of W. The entire derivative is its pointwise limit as t tends to zero through nonzero complex values. The finite-dimensional submodule is closed in the Hausdorff product topology, so the limit belongs to W. This constructs derivativeEnd from actual scalar derivatives; it is consumed by the generalized-eigenspace classification.")),
                Paragraph(Text("The complete translation span contains the original function, is invariant under every complex translation, and consists of entire functions when the generator is entire. These are the inputs to the direct holomorphic proof of the classical finite-translation-space mechanism. The source-specific pointwise realization and its analytic joins are repository-derived; no a.e. measurable-function theorem is substituted for an everywhere entire statement."))),
            DescribeRole.Theorem))));
}

