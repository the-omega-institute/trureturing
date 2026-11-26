using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class NamingRestrictionLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint distribution of a fixed selection of yet unnamed vertices.",
        H("Restricting a random injective naming"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("naming-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/NamingRestrictionLaw.namingMass"),
                H("Mass of one uniform outcome"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mass assigned to an outcome is the reciprocal of the cardinality " +
                    "of its naming space, represented in the extended nonnegative reals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-residual-restriction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/NamingRestrictionLaw.uniform_residual_restriction"),
                H("Joint uniformity on the selected vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix distinct names from a finite name set on a subset of a finite vertex set. " +
                        "Choose an available subset of names disjoint from the fixed names. Assume at least one " +
                        "injective completion exists whose remaining names are all available. " +
                        "Sample such a completion uniformly and restrict to a fixed injectively " +
                        "indexed selection of the remaining vertices.")),
                    Paragraph(Text(
                        "Every injection from the selection into the available name set has " +
                        "mass equal to the reciprocal of the total number of such injections.")),
                    Paragraph(Text(
                        "The consistent completions correspond to the residual injections. " +
                        "A permutation of the available names carrying one restricted naming " +
                        "to another gives a bijection of their completion fibers. The equal " +
                        "fiber masses sum to one."))),
                DescribeRole.Theorem))));
}
