using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyHankelRankDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/FinitePronyHankelRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct active Prony modes make every sufficiently long finite Hankel "
            + "section have rank equal to the mode count.",
        H("Finite Prony Hankel Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-hankel-rank"),
                DeclarationHandle.Create(Prefix + "finite_prony_hankel_rank"),
                H("Separated active modes give exact finite Hankel rank"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For at least as many observation rows as indexed modes, injective "
                            + "nodes and nonzero modal weights make the zero-shift finite "
                            + "Prony Hankel section have rank exactly equal to the mode count.")),
                    Paragraph(Text(
                        "The upper bound follows from the rectangular Vandermonde-diagonal-"
                            + "Vandermonde-transpose factorization. The lower bound comes from "
                            + "the nonsingular leading square block, whose Vandermonde and "
                            + "diagonal determinants are both nonzero.")),
                    Paragraph(Text(
                        "This is formula (1295.7). It is an exact finite-dimensional result and "
                            + "does not provide a smallest-singular-value bound, a noisy rank "
                            + "threshold, or an infinite Hankel-operator theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-mode-count-equals-hankel-rank"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_mode_count_eq_hankel_rank"),
                H("The active spectral mode count equals the finite Hankel state dimension"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the separated nonzero-weight regime, the indexed number of finite "
                            + "spectral modes is exactly the rank of every sufficiently long "
                            + "Hankel section.")),
                    Paragraph(Text(
                        "This equality supplies the finite state-dimension interface used by "
                            + "Prony structures, matrix-pencil identification, and minimal "
                            + "linear realization theory."))),
                DescribeRole.Theorem)),
        []));
}
