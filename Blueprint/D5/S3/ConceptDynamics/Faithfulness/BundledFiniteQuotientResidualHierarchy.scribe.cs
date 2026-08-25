using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class BundledFiniteQuotientResidualHierarchyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/BundledFiniteQuotientResidualHierarchy."
        + "bundled_finite_quotient_residual_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite nilpotent quotient observations form a sublanguage of the finite solvable "
            + "quotient observations, and their residual intersections are ordered in reverse.",
        H("Bundled Finite Quotient Residual Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("bundled-finite-quotient-residual-hierarchy"),
            DeclarationHandle.Create(Declaration),
            H("Restricting bundled quotient languages enlarges residuals"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation carrier is Mathlib's bundled finite-index normal "
                        + "subgroup type. Solvable and nilpotent languages are predicates on "
                        + "that carrier, so finiteness is already part of every channel.")),
                Paragraph(Text(
                    "A nilpotent quotient is solvable. The finite residual is the canonical "
                        + "intersection supplied by the adjacent joint-kernel theorem; the "
                        + "other residuals intersect only the bundled channels satisfying "
                        + "their respective predicates.")),
                Paragraph(Text(
                    "Intersecting over all finite quotients is contained in the solvable "
                        + "intersection, and the solvable intersection is contained in the "
                        + "nilpotent intersection. This closes atom generic-residual-"
                        + "1af9114aad5514c525c71e338c1ccb4f142b4afe6fedc0d198daa73a4e456caa."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula nilpotentLanguage = Call("nilpotentFiniteQuotientLanguage", group);
        Formula solvableLanguage = Call("solvableFiniteQuotientLanguage", group);
        Formula finiteResidual = Call("finiteResidual", group);
        Formula solvableResidual = Call("solvableFiniteResidual", group);
        Formula nilpotentResidual = Call("nilpotentFiniteResidual", group);

        return Disp(Seq(
            Forall, Sp, group, Comma, Sp, Call("Group", group), Sp, Rightarrow, RowBreak, Grp(),
            Open, nilpotentLanguage, Sp, Subseteq, Sp, solvableLanguage, Close,
            Sp, Land, RowBreak, Grp(),
            Open, finiteResidual, Sp, Subseteq, Sp, solvableResidual, Close,
            Sp, Land, RowBreak, Grp(),
            Open, solvableResidual, Sp, Subseteq, Sp, nilpotentResidual, Close, Dot));
    }
}
