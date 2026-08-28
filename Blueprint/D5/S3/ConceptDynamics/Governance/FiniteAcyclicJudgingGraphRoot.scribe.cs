using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class FiniteAcyclicJudgingGraphRootDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/FiniteAcyclicJudgingGraphRoot."
            + "finite_acyclic_judging_graph_has_root";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonempty acyclic judging graph has a vertex with no incoming judge.",
        H("Finite Acyclic Judging Graph Root"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-acyclic-judging-graph-has-root"),
                DeclarationHandle.Create(Declaration),
                H("A finite acyclic judging graph has a root"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "AcyclicEdge excludes a nonempty directed cycle in the judging relation. "
                            + "On a finite carrier, the transitive closure is therefore well-founded, "
                            + "and so is the original judging relation.")),
                    Paragraph(Text(
                        "The existing well-founded-frontier theorem applied to the full vertex "
                            + "set yields a ready vertex. Readiness against the complement of the "
                            + "full set says exactly that no vertex judges it.")),
                    Paragraph(Text(
                        "The result asserts only existence of an empty-judge vertex. It does not "
                            + "assert that this vertex certifies its own consistency."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula vertex = F.Id("V");
        Formula judges = F.Id("judges");
        Formula root = F.Id("r");
        Formula judge = F.Id("j");
        Formula proposition = F.Id("Prop");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, vertex, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Finite", vertex), Comma, Sp,
            Typeclass("Nonempty", vertex), Comma,
            RowBreak, Grp(),
            judges, Colon, Sp, Arrow(vertex, Arrow(vertex, proposition)), Comma,
            RowBreak, Grp(),
            Call("AcyclicEdge", judges), Sp, Rightarrow, Sp,
            Exists, Sp, root, Colon, Sp, vertex, Comma, Sp,
            Forall, Sp, judge, Colon, Sp, vertex, Comma, Sp,
            Neg, Sp, Apply(judges, judge, root), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
