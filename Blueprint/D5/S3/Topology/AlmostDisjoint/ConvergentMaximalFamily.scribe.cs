using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class ConvergentMaximalFamilyDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Statement => Disp(Seq(
        Ex("M", Call("Set", Call("Set", V("Word")))),
        Call("range", V("branchSet")), Sp, Subseteq, Sp, V("M"), Sp, Land, Sp, Call("MADFamily", V("M")),
        Sp, Land, Sp, All("A", Call("Set", V("Word"))), V("A"), Sp, InMacro, Sp, V("M"), Sp, Rightarrow, Sp,
        Ex("r", V("unitInterval")), Call("ConvergesOn", V("wordValue"), V("A"), V("r"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unrestricted convergent maximal family.", H("An unrestricted convergent maximal family"), Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Describe.Lean(
                DescribeId.Create("exists-convergent-mad"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily.exists_convergent_mad"),
                H("Actual maximal family containing the branches"), StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zorn extends the actual four-letter branch family among infinite almost-disjoint sets with convergent word values. Unions of chains preserve those requirements. An arbitrary infinite set almost disjoint from that maximal family has an injective sequence; compactness of unitInterval supplies a strictly increasing convergent subsequence. Its range would be a new convergent member, contradicting maximality. Thus every infinite set has infinite intersection with some member. The unrestricted maximality conclusion is proved rather than supplied as a hypothesis."))), DescribeRole.Theorem))));
}
