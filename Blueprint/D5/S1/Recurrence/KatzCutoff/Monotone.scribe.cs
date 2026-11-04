using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.KatzCutoff;

internal sealed class MonotoneDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Recurrence/KatzCutoff/Monotone.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/evansfrancisjones2025katz");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuants, path entries and Katz cut-offs.",
        H("Monotone"),
        Blocks(
            Paragraph(Text("Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.")),
            Node("RAB_strictMonoOn", All(V("a"), Naturals(), All(V("b"), Naturals(), ImpliesOf(Less(Num(0), V("a")), ImpliesOf(Less(Num(0), V("b")), Call("StrictMonoOn", LambdaOf(Alpha, Reals(), Call("RAB", Alpha, V("a"), V("b"))), Apply(Qualified("Set", "Ioo"), Num(0), FracOf(Num(1), Num(2)))))))), "The displayed identity or inequality is used to compare the path entries and their scalar crossing.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("R_strict_succ", All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), All(Alpha, Reals(), ImpliesOf(Less(Num(0), Alpha), ImpliesOf(Less(Alpha, FracOf(Num(1), Num(2))), Less(Call("RAB", Alpha, NatDiv(V("n"), Num(2)), NatDiv(Subtract(V("n"), Num(1)), Num(2))), Call("RAB", Alpha, NatDiv(Add(V("n"), Num(1)), Num(2)), NatDiv(Subtract(Add(V("n"), Num(1)), Num(1)), Num(2))))))))), "The displayed identity or inequality is used to compare the path entries and their scalar crossing.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, Formula formula, string text, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula ImpliesOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula LambdaOf(Formula name, Formula type, Formula body) => Parenthesized(Seq(V("fun"), Sp, name, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula NatDiv(Formula a, Formula b) => Apply(Qualified("Nat", "div"), a, b);
}
