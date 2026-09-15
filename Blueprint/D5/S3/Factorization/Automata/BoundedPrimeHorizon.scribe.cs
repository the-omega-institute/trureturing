using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class BoundedPrimeHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both guard distances, rather than current legality alone, determine the exact finite-horizon state.",
        H("Two-Boundary Observation of a Prime Register"),
        Blocks(
            Paragraph(Text(
                "The bounded runner records whether the entire requested word was legal. "
                + "At horizon H, compare "
                + "all words of total length at most H, including the empty word.")),
            Describe.Lean(
                DescribeId.Create("bounded-prime-horizon-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.finite_horizon_kernel"),
                H("The exact two-boundary profile"),
                StatementSource.FromAuthor(FiniteHorizonKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two live states have equal responses to every such word exactly when "
                    + "the displayed profiles agree. Necessity uses repeated multiplication "
                    + "and division. Sufficiency is induction over the word: first-step "
                    + "guards agree, and successful successors have equal profiles at H-1. "
                    + "Mixed paths, underflow and overflow are all covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-realized-profile-count"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.profile_classification"),
                H("Every profile is realized and counted"),
                StatementSource.FromAuthor(ProfileClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A concrete code collapses only the central interval. It is surjective "
                    + "onto Fin(min(a,2H)+1), and its kernel is exactly the response kernel. "
                    + "The separate rejection point remains visible on the empty word. "
                    + "This is not a claim that a fixed-H quotient updates autonomously "
                    + "for arbitrarily many later steps."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula FinState() => Call("Fin", Seq(F.Id("a"), Sp, Plus, Sp, D(1)));

    private static Formula Words() => Call("List", F.Id("Bool"));

    private static Formula BoundedResponse(string left, string right, string observation) => Seq(
        Open, Forall, Sp, F.Id("w"), Colon, Sp, Words(), Comma, Sp,
        Call("length", F.Id("w")), Sp, Leq, Sp, F.Id("H"), Sp, Rightarrow, Sp,
        Call(observation, F.Id("a"), F.Id(left), F.Id("w")), Sp, Eq, Sp,
        Call(observation, F.Id("a"), F.Id(right), F.Id("w")), Close);

    private static Formula FiniteHorizonKernelFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("H"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Forall, Sp, F.Id("e"), Comma, Sp, F.Id("f"), Colon, Sp, FinState(), Comma, Sp,
        BoundedResponse("e", "f", "accepts"), Sp, Iff, Sp,
        Call("close", F.Id("a"), F.Id("H"), F.Id("e"), F.Id("f"))));

    private static Formula MappedCode(string state) =>
        Call("map", Call("code", F.Id("a"), F.Id("H")), F.Id(state));

    private static Formula ProfileClassificationFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("H"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Call("Surjective", Seq(Open, F.Id("q"), Colon, Sp, Call("Option", FinState()), Close,
            Sp, Mapsto, Sp, MappedCode("q"))),
        Sp, Land, Sp,
        Open, Forall, Sp, F.Id("q"), Comma, Sp, F.Id("r"), Colon, Sp,
        Call("Option", FinState()), Comma, Sp,
        BoundedResponse("q", "r", "observed"), Sp, Iff, Sp,
        MappedCode("q"), Sp, Eq, Sp, MappedCode("r"), Close,
        Sp, Land, Sp,
        Call("card", Call("Option", Call("Fin", Seq(
            Call("min", F.Id("a"), Seq(D(2), Sp, Times, Sp, F.Id("H"))),
            Sp, Plus, Sp, D(1))))),
        Sp, Eq, Sp, Call("min", F.Id("a"), Seq(D(2), Sp, Times, Sp, F.Id("H"))),
        Sp, Plus, Sp, D(2)));
}
