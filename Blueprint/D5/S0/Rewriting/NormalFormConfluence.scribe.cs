using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NormalFormConfluenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Confluence makes reachable and equivalent normal forms unique.",
            H("Normal Form Confluence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("confluence-makes-reachable-normal-forms-unique"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/NormalFormConfluence.normal_form_unique_of_confluent"),
                    H("Reachable normal forms are unique"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("a"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow, Sp,
                        Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Close,
                        Sp, Rightarrow, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("n1"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("n2"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("IsNormalForm")), Open, F.Id("r"), Close,
                        Open, F.Id("n1"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("IsNormalForm")), Open, F.Id("r"), Close,
                        Open, F.Id("n2"), Close, Sp, Rightarrow, Sp,
                        F.Id("n1"), Sp, Eq, Sp, F.Id("n2"), Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(
                        Paragraph(Text(
                            "For a confluent rewrite relation, any two normal forms reachable "
                            + "from the same source are equal.")),
                        Paragraph(Text(
                            "A common successor supplied by confluence must equal each normal "
                            + "form because no nontrivial rewrite leaves a normal form."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("confluence-makes-equivalent-normal-forms-equal"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/NormalFormConfluence.eqvGen_normal_form_eq"),
                    H("Equivalent normal forms are equal"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("a"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow, Sp,
                        Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Close,
                        Sp, Rightarrow, Sp,
                        Operatorname, Grp(F.Id("EqvGen")), Open, F.Id("r"), Close,
                        Open, F.Id("n1"), Comma, Sp, F.Id("n2"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("IsNormalForm")), Open, F.Id("r"), Close,
                        Open, F.Id("n1"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("IsNormalForm")), Open, F.Id("r"), Close,
                        Open, F.Id("n2"), Close, Sp, Rightarrow, Sp,
                        F.Id("n1"), Sp, Eq, Sp, F.Id("n2"), Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(
                        Paragraph(Text(
                            "For a confluent rewrite relation, equivalent normal forms are "
                            + "equal even when their equivalence uses reverse rewrite steps.")),
                        Paragraph(Text(
                            "Induction on the generated equivalence produces a common successor; "
                            + "the transitive case rejoins its intermediate reductions by "
                            + "confluence."))),
                    DescribeRole.Theorem))));
}
