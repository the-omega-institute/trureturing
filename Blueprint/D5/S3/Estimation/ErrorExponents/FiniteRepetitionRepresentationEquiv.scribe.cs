using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteRepetitionRepresentationEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ErrorExponents/FiniteRepetitionRepresentationEquiv.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive IidSpace samples, product masses, distances, affinities and equal-prior decision risks transport exactly to the canonical Fin-indexed finite-suite representation.",
        H("Finite Repetition Representation Equivalence"),
        Blocks(
            Paragraph(Text(
                "The repository already uses two finite-product representations for different "
                    + "proof interfaces. This module connects them using Mathlib's Fin.consEquiv, "
                    + "then transports the existing product mass, total variation, "
                    + "Bhattacharyya affinity and decision events. It introduces no third "
                    + "repetition encoding or second Bayes-risk primitive.")),
            Describe.Lean(
                DescribeId.Create("carrier-equivalence"),
                DeclarationHandle.Create(Prefix + "iidSpaceFinEquiv"),
                H("Recursive iid samples are finite tuples"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IidSpace iota n is canonically equivalent to Fin n to iota. The "
                        + "successor step is Mathlib's canonical Fin.consEquiv."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successor-zero"),
                DeclarationHandle.Create(Prefix + "iid_space_fin_equiv_succ_zero"),
                H("The first tuple coordinate is the recursive head"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At successor length, coordinate zero of the transported tuple is exactly "
                        + "the head of the recursive sample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("successor-tail"),
                DeclarationHandle.Create(Prefix + "iid_space_fin_equiv_succ_succ"),
                H("Successor coordinates are the recursive tail"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every successor tuple coordinate is the corresponding coordinate of the "
                        + "recursively transported tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mass-transport"),
                DeclarationHandle.Create(Prefix + "iid_power_eq_windowLaw"),
                H("Recursive iid mass equals windowLaw"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the carrier equivalence, iidPower is pointwise exactly the existing "
                        + "windowLaw product of identical coordinate laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tv-transport"),
                DeclarationHandle.Create(Prefix + "total_variation_iidPower_eq_windowLaw"),
                H("Total variation is representation invariant"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite total variation agrees exactly between the recursive iid and "
                        + "Fin-indexed window representations after reindexing by the "
                        + "canonical equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affinity-transport"),
                DeclarationHandle.Create(Prefix + "bhattacharyya_iidPower_eq_windowLaw"),
                H("Bhattacharyya affinity is representation invariant"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Bhattacharyya affinity likewise agrees exactly under the same carrier and "
                        + "mass transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decision-transport"),
                DeclarationHandle.Create(Prefix + "iidDecisionToFin"),
                H("Decision events transport to finite tuples"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A recursive iid decision finset is mapped by the Finset action of the "
                        + "canonical carrier equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("decision-membership"),
                DeclarationHandle.Create(Prefix + "mem_iidDecisionToFin"),
                H("Decision membership is preserved"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tuple membership in the transported decision event is equivalent to "
                        + "membership of its inverse image in the recursive event."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decision-complement"),
                DeclarationHandle.Create(Prefix + "iidDecisionToFin_compl"),
                H("Decision transport preserves complements"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Transporting the complement of a recursive decision event equals the "
                        + "complement of the transported event."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decision-mass"),
                DeclarationHandle.Create(Prefix + "iid_decision_mass_eq_windowLaw"),
                H("Decision-event mass is representation invariant"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mass of every recursive iid decision event equals the windowLaw mass "
                        + "of its transported finite-tuple event."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decision-risk"),
                DeclarationHandle.Create(Prefix + "iid_equal_prior_error_eq_windowLaw"),
                H("Equal-prior testing risk is representation invariant"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every recursive iid decision has exactly the same equal-prior risk after "
                        + "transport to the finite-suite coordinates used by the operational "
                        + "finiteSuiteOptimalError owner."))),
                DescribeRole.Theorem))));
}
