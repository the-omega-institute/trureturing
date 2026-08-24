using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.QueryHierarchy;

internal sealed class QueryKernelHierarchyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collapse maps between query laws force a descending equality-kernel chain, and a "
            + "concrete three-layer query system realizes strictness in both steps.",
        H("Observation Intervention Counterfactual Kernel Hierarchy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("query-kernel-chain"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy.query_kernel_chain"),
                H("Query-law kernel chain"),
                StatementSource.FromAuthor(ChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generic clauses use explicit collapse maps between observation, "
                        + "intervention, and counterfactual laws, so equality of a richer profile "
                        + "is transported to every coarser profile."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-intervention-counterfactual-kernel-chain"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy."
                        + "observation_intervention_counterfactual_kernel_chain"),
                H("Both inclusions can be strict"),
                StatementSource.FromAuthor(StrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete three-coordinate query laws expose a pair witnessing each "
                        + "strict inclusion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Seq(Comma, Sp));
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ChainFormula() => Disp(Seq(
        Forall, Sp, F.Id("o"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("c"), Comma, Sp,
        F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        Call("ker", F.Id("c")), Sp, Subseteq, Sp, Call("ker", F.Id("i")), Sp,
        Land, Sp, Call("ker", F.Id("i")), Sp, Subseteq, Sp, Call("ker", F.Id("o"))));

    private static Formula StrictFormula() => Disp(Seq(
        Call("ker", F.Id("layeredCounterfactual")), Sp, Subseteq, Sp,
        Call("ker", F.Id("layeredIntervention")), Sp, Land, Sp,
        Call("ker", F.Id("layeredIntervention")), Sp, Subseteq, Sp,
        Call("ker", F.Id("layeredObservation")), Sp, Land, Sp,
        F.Id("strictnessWitnesses")));
}
