using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class OnlineVotingFourAlternativesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/ghasemi2026onlinevoting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every deterministic rule on four labeled alternatives and twelve labeled voters, "
            + "one fixed compatible election gives distortion above √13.",
        H("Four alternatives refute the deterministic √13 guarantee"),
        Blocks(
            Model("Alternative", "Alternative labels", Equal(F.Id("Alternative"), Call("Fin", Num(4))),
                "The four alternative labels are 0, 1, 2 and 3."),
            Model("Label", "Voter and alternative labels", LabelFormula(),
                "The left summand tags the n voters and the right summand tags the four alternatives. "
                + "Their locations in an election may coincide."),
            Model("Profile", "Full ballots", ProfileFormula(),
                "Each voter supplies an injective rank map on the four alternatives. "
                + "A smaller rank means an earlier ballot position."),
            Model("Arrival", "Arrival order",
                Equal(F.Id("Arrival"), Call("Equiv", Call("Fin", Num(4)), F.Id("Alternative"))),
                "The equivalence sends each arrival position to its alternative label."),
            Model("Observation", "Prefix observations",
                ForAll("n", F.Id("Nat"), Typed(Call("Observation", F.Id("n")), F.Id("Type"))),
                "The arrived field is a list of alternatives in arrival order. The prefers field "
                + "returns a Boolean for a voter in Fin n and an ordered pair of alternatives."),
            Model("observe", "Observing a ballot profile", ObserveFormula(),
                "The arrived field takes the first q labels in the arrival order. The prefers field "
                + "is true precisely when both arrival positions are less than q and the first "
                + "alternative has smaller full-ballot rank for that voter."),
            Model("Rule", "Deterministic rules", RuleFormula(),
                "A rule uses the ordered list of all observations so far and the list of its earlier "
                + "decisions. True switches to the latest arrival and false keeps the incumbent."),
            Model("finalWinner", "Final winner", WinnerFormula(),
                "The incumbent starts at the first arrival. For q equal to 2, 3 and 4, apply the rule "
                + "to observations 1 through q and the preceding decisions from rounds 2 through q − 1. "
                + "Keep the incumbent on false and replace it with the q-th arrival on true. "
                + "Return the incumbent at the end of round four."),
            Model("Election", "Compatible metric elections", ElectionFormula(),
                "An election carries a type Space with a MetricSpace structure, a location for each "
                + "Label, an Arrival and a Profile. For each voter and each pair of alternatives, "
                + "a strictly smaller candidate-to-voter distance requires a strictly smaller ballot rank. "
                + "Each full strict ballot orders distance ties consistently across all prefixes."),
            Model("socialCost", "Social cost", CostFormula(),
                "The sum uses the election's metric and includes every voter. The right injection "
                + "supplies the alternative label and the left injection supplies the voter label."),
            Describe.Lean(
                DescribeId.Create("four-alternative-distortion-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The four-alternative guarantee"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
                    Parenthesized(Guarantee())))),
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
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Guarantee())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Section 6 asks, “An interesting open question is whether this guarantee "
                        + "can be extended to elections with more than three alternatives, or whether "
                        + "additional alternatives necessarily lead to higher distortion.”")),
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
                        + "The four ratios are 5503/1503, 6503/1503, 11753/3253 and 7503/2003. "
                        + "The paper's §3 allows the canonical arrival order. A uniform extension "
                        + "to all horizons greater than three would have to cover this four-option, "
                        + "twelve-voter case."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Model(string name, string title, Formula formula, string description) =>
        Describe.Lean(DescribeId.Create("four-alternative-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(description))), DescribeRole.Definition);

    private static Formula LabelFormula()
    {
        Formula n = F.Id("n");
        return ForAll("n", F.Id("Nat"), Equal(Call("Label", n),
            Call("Sum", Call("Fin", n), F.Id("Alternative"))));
    }

    private static Formula ProfileFormula()
    {
        Formula n = F.Id("n");
        Formula rank = F.Id("rank");
        Formula alternative = F.Id("Alternative");
        Formula ballot = Seq(OpenBrace, rank, Colon, Sp, Arrow(alternative, alternative),
            Sp, Mid, Sp, Call("Injective", rank), CloseBrace);
        return ForAll("n", F.Id("Nat"), Equal(Call("Profile", n), Arrow(Call("Fin", n), ballot)));
    }

    private static Formula ObserveFormula()
    {
        Formula n = F.Id("n");
        Formula order = F.Id("o");
        Formula profile = F.Id("p");
        Formula round = F.Id("q");
        return ForAll("n", F.Id("Nat"),
            ForAll("o", F.Id("Arrival"), ForAll("p", Call("Profile", n), ForAll("q", F.Id("Nat"),
                Typed(Call("observe", order, profile, round), Call("Observation", n))))));
    }

    private static Formula RuleFormula()
    {
        Formula n = F.Id("n");
        Formula boolean = F.Id("Bool");
        return ForAll("n", F.Id("Nat"), Equal(Call("Rule", n),
            Parenthesized(Arrow(Call("List", Call("Observation", n)), Arrow(Call("List", boolean), boolean)))));
    }

    private static Formula WinnerFormula()
    {
        Formula n = F.Id("n");
        return ForAll("n", F.Id("Nat"), Typed(F.Id("finalWinner"),
            Arrow(Call("Rule", n), Arrow(F.Id("Arrival"), Arrow(Call("Profile", n), F.Id("Alternative"))))));
    }

    private static Formula ElectionFormula()
    {
        Formula n = F.Id("n");
        return ForAll("n", F.Id("Nat"), Typed(Call("Election", n), Seq(F.Id("Type"), Sp, Num(1))));
    }

    private static Formula CostFormula()
    {
        Formula n = F.Id("n");
        Formula election = F.Id("e");
        Formula alternative = F.Id("a");
        Formula candidate = Call("location", election, Call("inr", alternative));
        Formula voter = Call("location", election, Call("inl", F.Id("v")));
        Formula distance = Call("dist", candidate, voter);
        Formula sum = Seq(Sum, Underscore, Grp(Typed(F.Id("v"), Call("Fin", n))), Sp, distance);
        return ForAll("n", F.Id("Nat"), ForAll("e", Call("Election", n),
            ForAll("a", F.Id("Alternative"), Equal(Call("socialCost", election, alternative), sum))));
    }

    private static Formula Guarantee()
    {
        Formula rule = F.Id("r");
        Formula election = F.Id("e");
        Formula alternative = F.Id("a");
        Formula winner = Call("finalWinner", rule, Call("arrival", election),
            Call("profile", election));
        Formula bound = new Formula.Relation(Call("socialCost", election, winner),
            FormulaRelationOperator.LessThanOrEqual,
            Multiply(Seq(Sqrt, Grp(Num(13))), Call("socialCost", election, alternative)));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("r"), Call("Rule", Num(12)),
            ForAll("e", Call("Election", Num(12)), ForAll("a", F.Id("Alternative"), bound)));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
