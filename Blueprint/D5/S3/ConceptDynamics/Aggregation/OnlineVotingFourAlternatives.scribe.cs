using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class OnlineVotingFourAlternativesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/ghasemi2026onlinevoting");
    private static readonly ProblemSlugRef Problem =
        ProblemSlugRef.Create("ghasemi-seddighin-seddighin-2026-deterministic-metric-extension");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every deterministic rule with four labeled alternatives and twelve labeled voters "
            + "can exceed distortion √13 in a single fixed compatible election.",
        H("Four alternatives refute the deterministic √13 guarantee"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-alternative-distortion-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The four-alternative guarantee"),
                StatementSource.FromAuthor(Disp(Iff(F.Id("claim"), Guarantee()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Four labeled alternatives arrive in permutation order. Each of twelve labeled voters "
                        + "has a full strict ballot compatible with distances in a common metric. Strictly "
                        + "closer alternatives rank earlier, and each ballot orders ties consistently. "
                        + "At each arrival the rule sees all previous and current labeled prefix comparisons "
                        + "and arrival prefixes, along with its own earlier keep-or-switch decisions.")),
                    Paragraph(Text(
                        "The first arrival initializes the incumbent. Every later decision retains it or "
                        + "switches to the latest arrival. The social cost is the sum of the twelve voter "
                        + "distances. The comparison against every alternative expresses the guarantee "
                        + "against the attained minimum over the full election."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-alternative-distortion-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The deterministic guarantee fails at four alternatives"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The certificate uses the order 0, 1, 2, 3. The labeled six-to-six opening is "
                        + "shared by all leaves. Given the second decision, both fourth profiles extend "
                        + "the same third-round comparisons. Each fourth profile has two compatible "
                        + "metrics with the same full ballots, one for each fourth-round action. "
                        + "Computing the decisions selects one full election, whose run reproduces "
                        + "those decisions even when the rule uses all history and labels.")),
                    Paragraph(Text(
                        "The finite tables give metric inequalities, compatible rankings and exact "
                        + "social costs. Each leaf has a positive offline minimum, and its squared "
                        + "winner cost is strictly greater than thirteen times the squared minimum. "
                        + "The paper's §3 allows the canonical arrival order. A uniform extension "
                        + "to all horizons greater than three would have to cover this four-option, "
                        + "twelve-voter case."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(Problem, ResolutionKind.Refuted)))));

    private static Formula Guarantee()
    {
        Formula rule = F.Id("r");
        Formula election = F.Id("e");
        Formula alternative = F.Id("a");
        Formula winner = Call("finalWinner", rule, Call("arrival", election),
            Call("profile", election));
        Formula bound = Le(Call("socialCost", election, winner),
            Mul(Seq(Sqrt, Grp(Num(13))), Call("socialCost", election, alternative)));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("r"),
            Call("Rule", Num(12)),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("e"),
                Call("Election", Num(12)),
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("a"),
                    F.Id("Alternative"), bound)));
    }
}
