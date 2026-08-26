using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class AlexandrovInseparabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper-Alexandrov inseparability is mutual reachability and antisymmetry.",
        H("Alexandrov Inseparability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-inseparability-is-mutual-relation"),
                DeclarationHandle.Create(Prefix + "upper_inseparable_iff_mutual"),
                H("Upper-Alexandrov inseparability is mutual relatedness"),
                StatementSource.FromAuthor(MutualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equip a carrier with the topology of sets that are upward closed "
                            + "for a reflexive and transitive relation.")),
                    Paragraph(Text(
                        "The principal upset of either point is open. Inseparability forces "
                            + "each point into the other's principal upset, giving both "
                            + "relation directions.")),
                    Paragraph(Text(
                        "Conversely, mutual relatedness transports membership through every "
                            + "upper-open set in both directions, so no open set separates "
                            + "the points."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("antisymmetry-collapses-inseparability-to-equality"),
                DeclarationHandle.Create(Prefix + "antisymmetric_iff_inseparable_eq"),
                H("Antisymmetry is equality of inseparable points"),
                StatementSource.FromAuthor(AntisymmetryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the displayed reflexivity and transitivity instances, the "
                            + "preceding characterization identifies inseparability with two "
                            + "opposing relation steps.")),
                    Paragraph(Text(
                        "The relation is antisymmetric exactly when every such mutually "
                            + "related, and hence inseparable, pair is equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("acyclic-dependencies-separate-inseparable-points"),
                DeclarationHandle.Create(
                    Prefix + "dependency_inseparable_implies_eq_of_acyclic"),
                H("Acyclic dependency topology separates distinct points"),
                StatementSource.FromAuthor(AcyclicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Dependency reachability is reflexive and transitive. Acyclicity "
                            + "makes it antisymmetric because opposing nontrivial paths would "
                            + "compose to a cycle.")),
                    Paragraph(Text(
                        "Therefore two points inseparable in the dependency Alexandrov "
                            + "topology must coincide."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula RelationType(Formula carrier) =>
        Arrow(carrier, Arrow(carrier, Seq(Operatorname, Grp(F.Id("Prop")))));

    private static Formula RelationInstances(Formula carrier, Formula relation) =>
        Seq(
            OpenBracket, Call("Refl", relation), CloseBracket, Sp,
            OpenBracket, Call("IsTrans", carrier, relation), CloseBracket);

    private static Formula Inseparable(Formula relation, Formula first, Formula second) =>
        Call(
            "Inseparable",
            Call("upperSetTopology", relation),
            first,
            second);

    private static Formula MutualFormula()
    {
        Formula carrier = F.Id("V");
        Formula relation = F.Id("relation");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula mutual = Seq(
            Apply(relation, first, second), Sp, Land, Sp,
            Apply(relation, second, first));

        return Disp(Seq(
            Forall, Sp, relation, Colon, Sp, RelationType(carrier), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            RelationInstances(carrier, relation), Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Inseparable(relation, first, second), Sp, Iff, Sp, mutual,
            Close, Dot));
    }

    private static Formula AntisymmetryFormula()
    {
        Formula carrier = F.Id("V");
        Formula relation = F.Id("relation");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula relationPair = Seq(
            Apply(relation, first, second), Sp, Land, Sp,
            Apply(relation, second, first));
        Formula antisymmetry = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, carrier, Comma, Sp,
            Open, relationPair, Close, Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second);
        Formula inseparableEquality = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, carrier, Comma, Sp,
            Inseparable(relation, first, second), Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second);

        return Disp(Seq(
            Forall, Sp, relation, Colon, Sp, RelationType(carrier), Comma, RowBreak, Grp(),
            RelationInstances(carrier, relation), Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Open, antisymmetry, Close, Sp, Iff, Sp,
            Open, inseparableEquality, Close,
            Close, Dot));
    }

    private static Formula AcyclicFormula()
    {
        Formula carrier = F.Id("V");
        Formula edge = F.Id("edge");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula hypotheses = Seq(
            Call("AcyclicEdge", edge), Sp, Land, Sp,
            Call(
                "Inseparable",
                Call("dependencyTopology", edge),
                first,
                second));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp, RelationType(carrier), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second, Dot));
    }
}
