using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class AxiomClosureMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge-local monotone labels remain monotone along dependency reachability.",
        H("Axiom Closure Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-monotone-labels-are-reachability-monotone"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity."
                    + "label_mono_of_edge_mono"),
            H("Local label monotonicity extends to every reachable pair"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let every dependency edge carry the source label into the target "
                        + "label by set inclusion.")),
                Paragraph(Text(
                    "A reflexive-transitive reachability path is built from zero or more "
                        + "such edge steps. Induction on that path composes the inclusions.")),
                Paragraph(Text(
                    "Consequently, every atom attached at a reachable source is still "
                        + "present at the reachable target. No converse inclusion is claimed."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula vertex = F.Id("V");
        Formula atom = F.Id("Atom");
        Formula edge = F.Id("edge");
        Formula label = F.Id("label");
        Formula source = F.Id("u");
        Formula target = F.Id("v");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula edgeMonotone = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, vertex, Comma, Sp,
            Apply(edge, first, second), Sp, Rightarrow, Sp,
            Apply(label, first), Sp, Subseteq, Sp, Apply(label, second));
        Formula hypotheses = Seq(
            Open, edgeMonotone, Close, Sp, Land, Sp,
            Call("Reachable", edge, source, target));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp,
            Arrow(vertex, Arrow(vertex, Seq(Operatorname, Grp(F.Id("Prop"))))),
            Comma, RowBreak, Grp(),
            label, Colon, Sp, Arrow(vertex, Call("Set", atom)), Comma, Sp,
            source, Comma, Sp, target, Colon, Sp, vertex, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Apply(label, source), Sp, Subseteq, Sp, Apply(label, target), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
