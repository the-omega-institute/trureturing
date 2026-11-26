using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Measure;

internal sealed class ProductSupportIntersectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Almost-everywhere equal measurable nonnegative functions under a finite product probability law have a common measurable representative supported on the intersection of their coordinate sets.",
        H("Intersection of coordinate supports"), Blocks(
            Describe.Lean(DescribeId.Create("marginal-coordinate-dependence"),
                DeclarationHandle.Create("D5/S3/Analytic/Measure/ProductSupportIntersection.marginal_depends"),
                H("Integrating coordinates removes their dependencies"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let I be any coordinate type with decidable equality, X_i measurable spaces, " +
                    "mu_i arbitrary measures, and u a finite coordinate set. If an ENNReal " +
                    "function f on the dependent product depends only on S, then lmarginal(mu,u,f) " +
                    "depends only on S with u removed. No measurability of f, probability, " +
                    "sigma-finiteness, finite ambient index type or integral bound is assumed. " +
                    "Coordinates outside u are compared directly; the integrated coordinates " +
                    "are replaced by the same integration variable. This dependence statement " +
                    "identifies the supports of deleted rows in the Finner equality induction."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("product-support-intersection-representative"),
                DeclarationHandle.Create("D5/S3/Analytic/Measure/ProductSupportIntersection.exists_measurable_intersection_representative"),
                H("A common representative on the intersection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let I be any finite coordinate type, X_i arbitrary measurable spaces, " +
                        "mu_i probability measures, and mu their actual product measure. Let " +
                        "f,g:product_i X_i->ENNReal be measurable and mu-almost everywhere equal. " +
                        "Suppose f depends only on a set S of coordinates and g depends only " +
                        "on a set T. Then there is a measurable h depending only on S intersect T " +
                        "such that h=f and h=g mu-almost everywhere. No integrability, boundedness, " +
                        "topology or pointwise positivity is assumed. I, S and T may be empty.")),
                    Paragraph(Text(
                        "Take h to be the marginal of g obtained by integrating the coordinates " +
                        "outside S. This removes those coordinates from its possible dependencies, " +
                        "so h depends only on T intersect S. The same marginal of f equals f " +
                        "pointwise: f does not depend on the integrated coordinates and their " +
                        "product law has total mass one.")),
                    Paragraph(Text(
                        "To transport the almost-everywhere equality through marginal integration, " +
                        "let e be the indicator of f differing from g. Its integral is zero. " +
                        "Marginalization over a fixed coordinate set is idempotent under probability " +
                        "laws. Applying Mathlib's lintegral_eq_of_lmarginal_eq to the marginal of e " +
                        "and e shows that the marginal also has integral zero. Hence it vanishes " +
                        "almost everywhere. On every such slice, f and g agree almost everywhere " +
                        "under the integrated coordinate law, and their nonnegative integrals agree. " +
                        "Measurable.lmarginal supplies measurability of the resulting representative.")),
                    Paragraph(Text(
                        "This is a general product-measure support lemma. It gives no equality " +
                        "criterion for Finner's inequality by itself: normalized conditional factors " +
                        "must first be shown equal under one common product law, and any change " +
                        "of law must still be undone on each original factor, including slices " +
                        "of zero conditional mass. No mathematical priority is claimed."))),
                DescribeRole.Theorem))));
}
