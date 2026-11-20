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
                new OpenProblemResolutionClaim(Problem, ResolutionKind.Refuted)),
            Describe.Lean(
                DescribeId.Create("prescribed-horizon-distortion-lower-bound"),
                DeclarationHandle.Create(Prefix + "worst_case"),
                H("The lower bound holds at every prescribed horizon"),
                StatementSource.FromAuthor(Disp(PaddedBound())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "An order is an equivalence from the first four positions and k later "
                        + "positions to the candidate labels. For every such order and every "
                        + "deterministic rule on those labels, one compatible election has that "
                        + "order, a positive offline minimum and the displayed winner-cost bounds.")),
                    Paragraph(Text(
                        "The proof transports the same four metric leaves to the prescribed labels. "
                        + "Each fresh alternative is ranked after the old ones and costs 120012. "
                        + "Any later switch chooses a fresh alternative, and neither retaining the "
                        + "fourth-round winner nor switching to a fresh alternative decreases the "
                        + "cost. The benchmark still includes the entire extended election."))),
                DescribeRole.Theorem))));

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

    private static Formula PaddedBound()
    {
        Formula k = F.Id("k");
        Formula labels = F.Id("L");
        Formula order = F.Id("o");
        Formula rule = F.Id("r");
        Formula election = F.Id("e");
        Formula best = F.Id("b");
        Formula alternative = F.Id("a");
        Formula minimum = Call("cost", election, best);
        Formula winnerCost = Call("cost", election, Call("winner", rule, election));
        Formula ratio = new Formula.Fraction(Num(11753), Num(3253));
        Formula optimal = Bind(FormulaQuantifier.ForAll, "a", labels,
            Le(minimum, Call("cost", election, alternative)));
        Formula bounds = And(Le(Mul(ratio, minimum), winnerCost),
            new Formula.Relation(Mul(Seq(Sqrt, Grp(Num(13))), minimum),
                FormulaRelationOperator.LessThan, winnerCost));
        Formula positive = new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, minimum);
        Formula conditions = And(Equal(Call("order", election), order),
            And(optimal, And(positive, bounds)));
        Formula witnesses = Bind(FormulaQuantifier.Exists, "e", Call("Election", k, labels),
            Bind(FormulaQuantifier.Exists, "b", labels, conditions));
        return Bind(FormulaQuantifier.ForAll, "k", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "L", F.Id("Type"),
                Bind(FormulaQuantifier.ForAll, "o", Call("Order", k, labels),
                    Bind(FormulaQuantifier.ForAll, "r", Call("Rule", labels), witnesses))));
    }

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
