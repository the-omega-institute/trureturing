using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class AlexandrovDependencyTopologyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
                "Upper sets form the dependency Alexandrov topology with principal opens and " +
                "downset closures.",
        H("Alexandrov Dependency Topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-closure-is-the-principal-downset"),
                DeclarationHandle.Create(Prefix + "closure_singleton_eq_downset"),
                H("A singleton closes to its principal downset"),
                StatementSource.FromAuthor(ClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a reflexive and transitive relation and equip its carrier with "
                            + "the topology whose open sets are upward closed.")),
                    Paragraph(Text(
                        "The closure of a point consists exactly of the vertices that reach "
                            + "that point under the relation. This is the principal downset.")),
                    Paragraph(Text(
                        "The proof identifies specialization with the reverse relation and "
                            + "then applies the standard specialization characterization of "
                            + "singleton closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("principal-downsets-are-monotone"),
                DeclarationHandle.Create(Prefix + "downset_mono"),
                H("Principal downsets grow along the relation"),
                StatementSource.FromAuthor(DownsetMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For related vertices x and y, every predecessor of x is also a "
                            + "predecessor of y.")),
                    Paragraph(Text(
                        "Transitivity supplies the required composite relation step, so the "
                            + "principal downset at x is contained in the one at y."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula RelationType(Formula carrier) =>
        Arrow(carrier, Arrow(carrier, Seq(Operatorname, Grp(F.Id("Prop")))));

    private static Formula RelationHypotheses(Formula carrier, Formula relation) =>
        Seq(
            Call("Refl", relation), Sp, Land, Sp,
            Call("IsTrans", carrier, relation));

    private static Formula ClosureFormula()
    {
        Formula carrier = F.Id("V");
        Formula relation = F.Id("R");
        Formula point = F.Id("x");

        return Disp(Seq(
            Forall, Sp, relation, Colon, Sp, RelationType(carrier), Comma, Sp,
            point, Colon, Sp, carrier, Comma, Sp,
            Open, RelationHypotheses(carrier, relation), Close,
            Sp, Rightarrow, Sp,
            Call(
                "closure",
                Call("upperSetTopology", relation),
                Call("singleton", point)),
            Sp, Eq, Sp, Call("downset", relation, point), Dot));
    }

    private static Formula DownsetMonotonicityFormula()
    {
        Formula carrier = F.Id("V");
        Formula relation = F.Id("R");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula hypotheses = Seq(
            RelationHypotheses(carrier, relation), Sp, Land, Sp,
            Apply(relation, first, second));

        return Disp(Seq(
            Forall, Sp, relation, Colon, Sp, RelationType(carrier), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, carrier, Comma, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            Call("downset", relation, first), Sp, Subseteq, Sp,
            Call("downset", relation, second), Dot));
    }
}
