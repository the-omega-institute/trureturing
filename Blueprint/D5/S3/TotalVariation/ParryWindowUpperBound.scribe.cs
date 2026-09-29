using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryWindowUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryWindowUpperBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed minimizer tables for actual finite-k Parry windows.",
        H("Finite Parry window upper bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parry-window-upper-bound"),
                DeclarationHandle.Create(Prefix + "parry_window_upper_bound"),
                H("Fixed word orders and endpoint labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k >= 2 and 1 <= m <= R, let N = R-m+2 and p = parryParameter k. "
                    + "For either fixed tie convention, there are a permutation rho of all binary "
                    + "length-m words and a fixed binary label table beta such that the actual "
                    + "stationaryDefect of windowTable is at most 1/N + choose(N,2) p^(m-1). "
                    + "If beta is required to be identically zero, a fixed rho still attains "
                    + "2/N + choose(N,2) p^(m-1). False chooses the existing FairWindowMinimizer.table "
                    + "with leftmost ties; true chooses its rightmost variant, selecting the maximum "
                    + "position among the minimum-rank occurrences. The two constructions agree "
                    + "whenever the candidate words are distinct.")),
                    Paragraph(Text(
                    "The Bool/Fin 2 correspondence preserves the relation bits, while transport "
                    + "uses their complements. Both adjacent windows call the same deterministic "
                    + "table. On a collision-free context, the finite average over fixed word orders "
                    + "and label tables is exactly 1/N. For zero labels it is at most 2/N. "
                    + "A union bound over pairs of starts uses the actual overlapping Parry "
                    + "collision estimate, giving the stated correction. Finite averaging then "
                    + "selects fixed tables, which may depend on k, R and m. This construction "
                    + "introduces no online randomness or independent priorities for occurrences."))),
                DescribeRole.Theorem))));
}
