using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class WeightedHankelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing the quadratic weight by scalar differentiation.",
        H("Removing the quadratic weight by scalar differentiation"),
        Blocks(Describe.Lean(DescribeId.Create("quadratic-weighted-hankel-translation"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/WeightedHankel.finite_translation_space_of_weighted"),
            H("Removing the quadratic weight by scalar differentiation"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every entire complex f, finite entire separation of (z-w)^2*f(z+w) implies finite dimension of the complete span of its complex translates. The proof never divides by the quadratic factor on its zero diagonal.")),
                Paragraph(Text("The operator partial_z minus partial_w annihilates the dependence on z+w. Applying it twice to the weighted kernel gives exactly 8*f(z+w). Differentiating a finite separated sum preserves finite separation, so the unweighted Hankel kernel is finitely separated and the translation-span result applies.")),
                Paragraph(Text("The product-rule calculation takes place on scalar entire functions. It is an intermediate part of the complete finite-separation iff exponential-polynomial theorem. It supplies no spectral, entropy or physical realization assumption."))),
            DescribeRole.Theorem))));
}

