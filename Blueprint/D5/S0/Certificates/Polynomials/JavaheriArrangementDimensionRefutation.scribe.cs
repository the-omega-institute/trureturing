using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Polynomials;

internal sealed class JavaheriArrangementDimensionRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/javaheri2026arrangement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic arrangement conjecture fails at the nonnegative parameters a=6 and b=1.",
        H("A counterexample to the cyclic arrangement conjecture"),
        Blocks(
            Paragraph(Text(
                "Javaheri's arXiv:2610.33653v1 Conjecture 1.3 identifies the largest "
                    + "dimension in which a cyclic power inequality holds with the largest "
                    + "dimension selected by a sine threshold. The formal statement keeps "
                    + "the real nonnegative parameter domain, the cyclic successor, the "
                    + "extended-natural least-upper-bound definition of the valid dimension, "
                    + "and the greatest-element definition of the threshold dimension.")),
            Describe.Lean(
                DescribeId.Create("cyclic-arrangement-conjecture-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result"),
                H("The universal dimension identity is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "At a=6 and b=1, the threshold set has greatest element 3. "
                            + "The positive cyclic triple (6,5,5) makes the difference "
                            + "between the two sides equal to 364, so dimension 3 is not "
                            + "valid. The least-upper-bound specification of a valid "
                            + "dimension therefore cannot equal the threshold greatest "
                            + "element, contradicting the universal conjecture."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("javaheri-2026-cyclic-arrangement-conjecture-refutation"),
                    ResolutionKind.Refuted))),
        []));
}
