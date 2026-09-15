using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class DistinctCycleSizeLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit";

    private static LibraryNoteRef SourceNote => LibraryNoteRef.Create("D5/L/kotesovec2026a398726");
    private static LibraryNoteRef CountingNote => LibraryNoteRef.Create("D5/L/tauceti2026classsizes");
    private static LibraryNoteRef BookNote => LibraryNoteRef.Create("D5/L/flajolet2009analytic");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");
    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Named(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Invoke(string name, Formula value) => Seq(Named(name), Paren(value));
    private static Formula CastReal(Formula value) => Paren(Seq(value, Colon, Reals));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Colon, domain, Comma, Sp, body);
    private static Formula Permutations => Seq(Qualified("Equiv", "Perm"),
        Paren(Seq(Named("Fin"), Sp, N)));
    private static Formula DistinctSizes => Invoke("DistinctCycleSizes", SigmaLower);
    private static Formula SourceSum => Invoke("CycleSizeSum", N);
    private static Formula PartitionSet => Seq(SigmaLower, Dot, Named("partition"), Dot,
        Named("parts"), Dot, Named("toFinset"));
    private static Formula DistinctDefinition => All(N, Naturals,
        All(SigmaLower, Permutations, Seq(DistinctSizes, Eq, PartitionSet)));
    private static Formula SumDefinition => All(N, Naturals,
        Seq(SourceSum, Eq, Sum, Underscore, Grp(SigmaLower, Colon, Permutations), Sp,
            Sum, Underscore, Grp(K, InMacro, DistinctSizes), Sp, K));
    private static Formula Ratio => new Formula.Fraction(CastReal(SourceSum),
        Seq(CastReal(N), Cdot, CastReal(Seq(Qualified("Nat", "factorial"), Paren(N)))));
    private static Formula FullResult => Seq(Qualified("Filter", "Tendsto"), Paren(Seq(
        Paren(Seq(N, Colon, Naturals, Mapsto, Ratio)), Comma,
        Qualified("Filter", "atTop"), Comma, Invoke("nhds", CastReal(D(1))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total weight of distinct cycle lengths over all permutations is asymptotic to n times n factorial.",
        H("The Distinct Cycle Size Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distinct-cycle-sizes"),
                DeclarationHandle.Create(Module + ".DistinctCycleSizes"),
                H("Distinct lengths in a permutation"),
                StatementSource.FromAuthor(Disp(DistinctDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The partition of a permutation records every cycle length, including one "
                    + "for each fixed point. Passing from its multiset of parts to a finite set "
                    + "retains each length once. Thus fixed points contribute length one when "
                    + "present, regardless of their multiplicity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cycle-size-sum"),
                DeclarationHandle.Create(Module + ".CycleSizeSum"),
                H("The sum over all permutations"),
                StatementSource.FromAuthor(Disp(SumDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "For each permutation of Fin n, sum its distinct lengths and then sum "
                    + "over all permutations. This is the natural-valued statistic A398726. "
                    + "The empty permutation contributes zero; the statistic weights each "
                    + "distinct length by its size."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distinct-cycle-size-limit"),
                DeclarationHandle.Create(Module + ".result"),
                H("Kotesovec's normalized limit"),
                StatementSource.FromAuthor(Disp(FullResult)),
                AssessedProvenance.FromRepo(SourceNote, CountingNote, BookNote),
                Blocks(
                    Paragraph(Text(
                        "The real ratio of the complete statistic to n times n factorial "
                        + "tends to one along every sufficiently large natural index. The "
                        + "denominator is positive for n greater than zero; its zero-index "
                        + "value does not affect the limit.")),
                    Paragraph(Text(
                        "Cauchy's class-size formula transfers the uniform permutation sum "
                        + "to partitions with weight one over the product of k to the power "
                        + "m_k times m_k factorial, where m_k is the multiplicity of part k. "
                        + "These weights sum to one, including the empty partition. The "
                        + "full-partition formulation adapts the cited TauCeti proof.")),
                    Paragraph(Text(
                        "Removing two parts of length k injects partitions having at least "
                        + "two such parts into partitions of n minus twice k. The exact weight "
                        + "relation bounds the weighted second factorial moment by one over "
                        + "k squared. The average lost weight from repeated lengths is consequently "
                        + "nonnegative and at most the harmonic sum from one to n. Dividing "
                        + "by n gives a quantity tending to zero by the Cesaro theorem, "
                        + "which proves the stated limit."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a398726-distinct-cycle-size-limit"),
                    ResolutionKind.Proved)))));
}
