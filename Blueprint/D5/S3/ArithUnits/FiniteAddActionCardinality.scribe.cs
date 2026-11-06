using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class FiniteAddActionCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive actions turn invariant supports into divisibility statements.",
        H("Finite Additive Actions and Support Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-finset-empty-or-univ-of-pretransitive"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/FiniteAddActionCardinality.invariant_finset_empty_or_univ_of_pretransitive"),
                H("A pretransitive invariant support is empty or full"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite type carrying a pretransitive additive group action, a Finset "
                        + "whose image is unchanged by every group element is either empty or the "
                        + "whole state space. The proof transports one chosen support point to an "
                        + "arbitrary target, so the conclusion is an orbit statement rather than a "
                        + "pointwise accident."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("card-add-group-dvd-of-free-finite-action"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_free_finite_action"),
                H("A free finite action forces group-order divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite additive groups and finite state spaces, freeness makes every "
                        + "nonempty orbit have the same size as the acting group. Burnside's fixed "
                        + "point sum therefore yields that the acting group cardinality divides the "
                        + "state-space cardinality. This records the arithmetic content of orbit "
                        + "decomposition directly in Lean."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("card-add-group-dvd-of-invariant-finset-of-free-action"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_finset_of_free_action"),
                H("A free invariant support inherits group-order divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a finite support is invariant under a free additive action, the action "
                        + "restricts to its subtype. Applying the orbit count there proves that the "
                        + "group cardinality divides the support cardinality. In the affine "
                        + "commutator setting, a nonzero prime-field translation supplies exactly "
                        + "this free action, turning the commutator into a numerical obstruction on "
                        + "the support."))),
                DescribeRole.Theorem
            ))));
}
