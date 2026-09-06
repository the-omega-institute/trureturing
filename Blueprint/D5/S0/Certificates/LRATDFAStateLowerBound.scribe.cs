using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LRATDFAStateLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A kernel-checked LRAT refutation of any certified "
            + "finite-prefix encoding rules out every globally correct DFAO "
            + "within the same state budget.",
        H("LRAT Certificates for Sparse DFAO State Lower Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-global-model-from-prefix-refutation"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/LRATDFAStateLowerBound.no_global_model_at_most_of_prefix_refutation"),
                H("Finite-prefix refutation gives a global bounded-state exclusion"),
                StatementSource.FromAuthor(ExclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here E is a certified encoding of the prefix-model predicate for the sparse problem P at extent e and state budget b. Global correctness implies finite-prefix fitting; the certified encoding turns any prefix model into a satisfying valuation, while the Mathlib LRAT empty-clause proof excludes every such valuation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimal-state-count-from-prefix-refutation"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/LRATDFAStateLowerBound.minimal_state_count_of_prefix_refutation"),
                H("An upper machine and a lower refutation prove exact minimality"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here E is a certified encoding of the prefix-model predicate for P at extent e and state budget s minus one. A globally correct machine at the proposed state count supplies the upper bound. Refuting every finite-prefix model below that count supplies the lower bound, so exact typed state minimality follows."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula ExclusionFormula() => Disp(Seq(
        Call("Refutation", Call("formula", F.Id("E"))),
        Sp, Implies, Sp,
        Neg, Call("HasGlobalModelAtMost", F.Id("P"), F.Id("b"))));

    private static Formula MinimalityFormula() => Disp(Seq(
        Call("HasGlobalModel", F.Id("P"), F.Id("s")),
        Sp, Land, Sp,
        Call("Refutation", Call("formula", F.Id("E"))),
        Sp, Implies, Sp,
        Call("IsMinimalStateCount", F.Id("P"), F.Id("s"))));
}
