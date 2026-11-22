using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/Result.";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/AdditiveNumberTheory/benfieldlippard2025positivepowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sizes of the stable exception sets have strict adjacent rises and falls in every tail.",
        H("Oscillation of stable exception-set sizes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exception-set-oscillation"),
                DeclarationHandle.Create(Prefix + "conjecture_10_5"),
                H("Benfield–Lippard Conjecture 10.5"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Paper),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 10.5 (p. 10). The sequence |Bₖ| for k = 2, 3, … never becomes monotone. "

                        + "For every exponent k ≥ 2, there is a finite set B(k) that equals the set of positive offsets s missing from the sums j+s of exactly j positive kth powers, for every sufficiently large j. "
                        + "The j bases are indexed by Fin j and may repeat.")),
                    Paragraph(Text(
                        "Given a cutoff N ≥ 2, choose a prime p ≥ max(193,N+2). "
                        + "The lower bound at p−1 exceeds the upper bounds at the two odd exponents p−2 and p. "
                        + "Thus the strict rise at p−2 and the strict fall at p−1 both lie in the prescribed tail."))
                ),
                DescribeRole.Theorem)
        )));
}
