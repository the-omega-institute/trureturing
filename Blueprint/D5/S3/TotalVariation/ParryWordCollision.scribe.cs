using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryWordCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryWordCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional Parry word masses and overlapping collisions.",
        H("Conditional Parry words and collisions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parry-word-mass"),
                DeclarationHandle.Create(Prefix + "parry_word_mass"),
                H("Conditional word mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k >= 2, put p = parryParameter k and h = suffixWeight k p. "
                    + "Starting at any signed suffix state, the mass of every supported path of n "
                    + "transitions is p^n times h at its endpoint divided by h at its start. "
                    + "The transition factors telescope. A relation bit and a signed state determine "
                    + "at most one supported next state, so any specified relation word has at most "
                    + "one supported state path. Consequently, for every m >= 1 its conditional "
                    + "mass is at most p^(m-1), including mass zero for inadmissible words. "
                    + "The estimate uses the actual Parry inequalities p <= h_j <= 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parry-overlapping-collision"),
                DeclarationHandle.Create(Prefix + "parry_overlapping_collision"),
                H("Overlapping complete words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k >= 2 and m >= 1, take two starts a < b with b+m <= n in a complete "
                    + "n-transition prefix under the signed stationary Parry law. The probability "
                    + "that their length-m relation words agree is at most p^(m-1). "
                    + "After the prefix before b is fixed, equality determines every bit of the "
                    + "second word: a required bit either lies in that prefix or is an earlier "
                    + "already determined bit of the second word. This induction includes overlap. "
                    + "Summing the unused suffix uses the stochastic kernel row sums; averaging "
                    + "over the prefix uses the actual normalized Parry law. The two occurrences "
                    + "need not be independent."))),
                DescribeRole.Theorem))));
}
