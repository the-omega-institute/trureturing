using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class StrongComponentQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quotienting a directed relation by mutual reachability yields a partial order of strong "
            + "components.",
        H("Strong Component Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("component-reachability-is-antisymmetric"),
                DeclarationHandle.Create(Prefix + "componentReachable_antisymm"),
                H("Component reachability is antisymmetric"),
                StatementSource.FromAuthor(AntisymmetryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two strong components. If each component reaches the other under the "
                            + "quotient reachability relation, the components are equal.")),
                    Paragraph(Text(
                        "Mutual reachability was already used to form each quotient class; this "
                            + "theorem supplies the antisymmetry needed by the partial-order "
                            + "instance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-component-reachability-is-acyclic"),
                DeclarationHandle.Create(Prefix + "no_strict_component_cycle"),
                H("Strict component reachability has no cycle"),
                StatementSource.FromAuthor(AcyclicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any strong component, there is no nonempty cycle made of steps that "
                            + "reach forward without reaching backward.")),
                    Paragraph(Text(
                        "The displayed strict-component relation abbreviates forward component "
                            + "reachability together with failure of reverse reachability."))),
                DescribeRole.Theorem))));

    private static Formula AntisymmetryFormula()
    {
        Formula edge = F.Id("edge");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula hypotheses = Seq(
            Call("componentReachable", edge, first, second), Sp, Land, Sp,
            Call("componentReachable", edge, second, first));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, Call("StrongComponent", edge),
            Comma, RowBreak, Grp(), Open, hypotheses, Close, Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second, Dot));
    }

    private static Formula AcyclicFormula()
    {
        Formula edge = F.Id("edge");
        Formula component = F.Id("component");
        Formula strict = Call("strictComponentReachability", edge);

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            component, Colon, Sp, Call("StrongComponent", edge), Comma,
            RowBreak, Grp(),
            Neg, Sp, Call("TransGen", strict, component, component), Dot));
    }
}
