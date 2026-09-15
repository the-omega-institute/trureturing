using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeBoxBidirectionalHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered mixed-register words have a shared-state semantics and an exact product profile.",
        H("Bidirectional Prime-Box Horizon"),
        Blocks(
            Paragraph(Text(
                "A command specifies a register and either multiplication or exact division. "
                + "The initial state is one capacity-bounded exponent tuple. Commands retain "
                + "their order within each register, while different registers act independently.")),
            Describe.Lean(
                DescribeId.Create("prime-box-exact-bidirectional-profile"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon.mixed_word_profile_classification"),
                H("Exact cardinality at every capacity vector and every horizon"),
                StatementSource.FromAuthor(MixedWordClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Projecting a mixed word onto one register never increases its "
                        + "length. Conversely, every single-register word can be lifted to "
                        + "a mixed word using that register alone. These two constructions "
                        + "prove the exact product response kernel. Coordinate-wise "
                        + "surjectivity realizes every claimed profile, and finite product "
                        + "cardinality gives the displayed count including rejection.")),
                    Paragraph(Text(
                        "For the original capacities (4,2,1,1), counts are 2,37,61 at "
                        + "horizons 0,1,2. The target remains guard legality. The number of "
                        + "full live states has not fallen from 60; the availability of "
                        + "division shortens distinguishing experiments. Invalid attempts "
                        + "are observed as failure, not silently removed from the domain. "
                        + "No sparse base-4 DFAO conjecture is claimed solved."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/BoundedPrimeHorizon")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/PrimeCapacityHorizon"))
        ]));

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

    private static Formula Capacity() => Seq(
        Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp,
        Call("Fin", Seq(Call("a", F.Id("i")), Sp, Plus, Sp, D(1))));

    private static Formula Profile() => Call("Profile", F.Id("a"), F.Id("H"));

    private static Formula Allowed(string state) =>
        Call("allowed", F.Id("a"), F.Id(state), F.Id("w"));

    private static Formula MixedWordClassificationFormula() => Disp(Seq(
        Forall, Sp, F.Id("I"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Open, Call("DecidableEq", F.Id("I")), Sp, Land, Sp, Call("Fintype", F.Id("I")), Close,
        Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("a"), Colon, Sp, F.Id("I"), Sp, To, Sp, Naturals(), Comma, Sp,
        Forall, Sp, F.Id("H"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Call("Surjective", Call("boxCode", F.Id("a"), F.Id("H"))), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("q"), Comma, Sp, F.Id("r"), Colon, Sp,
        Call("Option", Capacity()), Comma, Sp,
        Open, Forall, Sp, F.Id("w"), Colon, Sp,
        Call("List", Seq(F.Id("I"), Sp, Times, Sp, F.Id("Bool"))), Comma, Sp,
        Call("length", F.Id("w")), Sp, Leq, Sp, F.Id("H"), Sp, Rightarrow, Sp,
        Open, Allowed("q"), Sp, Iff, Sp, Allowed("r"), Close, Close,
        Sp, Iff, Sp,
        Call("boxCode", F.Id("a"), F.Id("H"), F.Id("q")), Sp, Eq, Sp,
        Call("boxCode", F.Id("a"), F.Id("H"), F.Id("r")), Close,
        Sp, Land, Sp,
        Call("card", Call("Option", Profile())), Sp, Eq, Sp, D(1), Sp, Plus, Sp,
        Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp,
        Open, Call("min", Call("a", F.Id("i")), Seq(D(2), Sp, Times, Sp, F.Id("H"))),
        Sp, Plus, Sp, D(1), Close));
}
