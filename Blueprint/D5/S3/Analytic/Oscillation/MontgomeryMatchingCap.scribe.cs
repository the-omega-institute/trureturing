using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryMatchingCapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryMatchingCap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint close-pair defects amplify into a strict Lorentz cap under a zero-phase bound.",
        H("Disjoint close-pair defects and a strict Lorentz cap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-matching-defect"),
                DeclarationHandle.Create(Owner + ".finite_matching_defect"),
                H("Finite matching defect inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite collection of copies carries the inclusive closed radius-one neighborhoods. Two injective endpoint maps with disjoint images ensure that every selected row is counted once.")),
                    Paragraph(Text("In the first endpoint neighborhood the two Lorentz weights are at least four fifths and one half. For the two chord lengths to a neighboring phase, the square of their sum is at most thirteen fourths of their weighted squared sum. The triangle inequality therefore gives four thirteenths of the endpoint phase residual per neighboring copy. All omitted terms are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectrum-matching-defect"),
                DeclarationHandle.Create(Owner + ".spectrum_matching_defect"),
                H("Defect for a spectrum with multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite set of sigma-indexed copies counts each ordinate with its multiplicity through the inclusive cutoff. The copy-sum expansion identifies the ordered deficit with the difference of the Montgomery sums at zero and at the tested frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-normalized-cap-of-matching"),
                DeclarationHandle.Create(Owner + ".strict_normalized_cap_of_matching"),
                H("Conditional normalized cap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a cutoff above one, lower bounds proportional to the cutoff times its logarithm for the matching size and to its logarithm for the neighborhood copy counts, together with a nonnegative phase residual lower bound, give a normalized saving of at least four thirteenths of the product of their three constants.")),
                    Paragraph(Text("If the normalized zero-phase sum is at most the target cap minus the chosen margin plus that saving, the normalized sum at the tested frequency is at most the target cap minus the margin. A positive margin gives a strict bound. Obtaining sufficiently many such close pairs with a uniform phase residual for actual zeta zeros across a long frequency band remains open."))),
                DescribeRole.Theorem))));
}
