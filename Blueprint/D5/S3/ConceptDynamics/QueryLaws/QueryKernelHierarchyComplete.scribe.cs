using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.QueryLaws;

internal sealed class QueryKernelHierarchyCompleteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The public theorem combines the generic query-law kernel chain with explicit "
            + "witnesses for strictness in both inclusions.",
        H("Complete Query Kernel Hierarchy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("query-kernel-hierarchy-complete"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/QueryLaws/QueryKernelHierarchyComplete."
                        + "query_kernel_hierarchy_complete"),
                H("Query-law kernel hierarchy with strictness"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first public conjunct is generic in the model and law carriers and "
                        + "uses only the two source collapse premises. The remaining conjuncts "
                        + "are concrete Boolean-coordinate countermodels."))),
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

    private static Formula Formula() => Disp(Seq(
        Call("ker", F.Id("counterfactualLaw")), Sp, Subseteq, Sp,
        Call("ker", F.Id("interventionLaw")), Sp, Land, Sp,
        Call("ker", F.Id("interventionLaw")), Sp, Subseteq, Sp,
        Call("ker", F.Id("observationLaw")), Sp, Land, Sp,
        F.Id("strictnessWitnesses")));
}
