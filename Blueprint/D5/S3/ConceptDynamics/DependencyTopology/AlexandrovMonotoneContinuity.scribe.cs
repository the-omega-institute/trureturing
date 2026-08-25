using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class AlexandrovMonotoneContinuityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maps between upper Alexandrov spaces are continuous exactly when they are monotone.",
        H("Alexandrov Monotone Continuity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-alexandrov-continuity-is-monotonicity"),
                DeclarationHandle.Create(
                    Prefix + "continuous_upperSetTopology_iff_monotone"),
                H("Continuity between upper Alexandrov spaces is monotonicity"),
                StatementSource.FromAuthor(ContinuityIffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix reflexive and transitive relations on the source and target and "
                            + "give each carrier its upper-set Alexandrov topology.")),
                    Paragraph(Text(
                        "Continuity pulls the principal upset of a mapped source point back "
                            + "to an open source set. Upward closure of that preimage forces "
                            + "the map to preserve the relation.")),
                    Paragraph(Text(
                        "Conversely, a relation-preserving map sends every source relation "
                            + "step to a target relation step, so preimages of target upper "
                            + "sets are upper and therefore open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monotone-dependency-map-is-continuous"),
                DeclarationHandle.Create(
                    Prefix + "monotone_continuous_dependencyTopology"),
                H("A monotone dependency map is continuous"),
                StatementSource.FromAuthor(DependencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RelationMonotone here means that the map preserves reflexive-"
                            + "transitive dependency reachability from the source graph to "
                            + "the target graph.")),
                    Paragraph(Text(
                        "Applying the upper-Alexandrov equivalence to those two reachability "
                            + "relations yields continuity between the corresponding "
                            + "dependency topologies."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula RelationType(Formula carrier) =>
        Arrow(carrier, Arrow(carrier, Seq(Operatorname, Grp(F.Id("Prop")))));

    private static Formula RelationInstances(Formula carrier, Formula relation) =>
        Seq(
            OpenBracket, Call("Refl", relation), CloseBracket, Sp,
            OpenBracket, Call("IsTrans", carrier, relation), CloseBracket);

    private static Formula ContinuityIffFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula sourceRelation = F.Id("relationX");
        Formula targetRelation = F.Id("relationY");
        Formula map = F.Id("map");
        Formula continuity = Call(
            "Continuous",
            Call("upperSetTopology", sourceRelation),
            Call("upperSetTopology", targetRelation),
            map);
        Formula monotonicity = Call(
            "RelationMonotone",
            sourceRelation,
            targetRelation,
            map);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, sourceRelation, Colon, Sp, RelationType(source), Comma, Sp,
            targetRelation, Colon, Sp, RelationType(target), Comma, Sp,
            map, Colon, Sp, Arrow(source, target), Comma, RowBreak, Grp(),
            RelationInstances(source, sourceRelation), Sp,
            RelationInstances(target, targetRelation), Sp,
            Rightarrow, RowBreak, Grp(),
            Open, continuity, Sp, Iff, Sp, monotonicity, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DependencyFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula sourceEdge = F.Id("edgeX");
        Formula targetEdge = F.Id("edgeY");
        Formula map = F.Id("map");
        Formula monotonicity = Call(
            "RelationMonotone",
            Call("Reachable", sourceEdge),
            Call("Reachable", targetEdge),
            map);
        Formula continuity = Call(
            "Continuous",
            Call("dependencyTopology", sourceEdge),
            Call("dependencyTopology", targetEdge),
            map);

        return Disp(Seq(
            Forall, Sp, sourceEdge, Colon, Sp, RelationType(source), Comma, Sp,
            targetEdge, Colon, Sp, RelationType(target), Comma, Sp,
            map, Colon, Sp, Arrow(source, target), Comma, RowBreak, Grp(),
            monotonicity, Sp, Rightarrow, RowBreak, Grp(),
            continuity, Dot));
    }
}
