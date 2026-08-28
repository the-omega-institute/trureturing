using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class DependencyReachabilityOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclic dependency reachability is a partial order.",
        H("Dependency Reachability Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("acyclic-reachability-is-a-partial-order"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder."
                    + "reachable_partial_order"),
            H("Acyclic reachability has the three partial-order laws"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Reachable is the reflexive-transitive closure of the supplied edge "
                        + "relation, while StrictReachable requires at least one edge.")),
                Paragraph(Text(
                    "Reflexivity and transitivity follow from the closure construction. "
                        + "Acyclicity rules out strict paths that return to their source.")),
                Paragraph(Text(
                    "If two vertices reach one another and are distinct, their two strict "
                        + "paths compose to a forbidden cycle. Thus mutual reachability "
                        + "forces equality."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula vertex = F.Id("V");
        Formula edge = F.Id("edge");
        Formula source = F.Id("u");
        Formula target = F.Id("v");
        Formula reachable = Call("Reachable", edge);
        Formula antisymmetric = Seq(
            Forall, Sp, source, Comma, Sp, target, Colon, Sp, vertex, Comma, Sp,
            Open,
            Call("Reachable", edge, source, target), Sp, Land, Sp,
            Call("Reachable", edge, target, source),
            Close, Sp, Rightarrow, Sp,
            source, Sp, Eq, Sp, target);
        Formula laws = Seq(
            Call("Reflexive", reachable), Sp, Land, Sp,
            Call("Transitive", reachable), Sp, Land, RowBreak, Grp(),
            Open, antisymmetric, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp,
            Arrow(vertex, Arrow(vertex, Seq(Operatorname, Grp(F.Id("Prop"))))),
            Comma, RowBreak, Grp(),
            Call("AcyclicEdge", edge), Sp, Rightarrow, RowBreak, Grp(),
            Open, laws, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
