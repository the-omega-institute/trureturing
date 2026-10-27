using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.KatzCutoff;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Recurrence/KatzCutoff/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/evansfrancisjones2025katz");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuants, path entries and Katz cut-offs.",
        H("Result"),
        Blocks(
            Paragraph(Text("Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.")),
            Node("claim", Equal(V("claim"), Parenthesized(Conj(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Some(V("a"), Reals(), Conj(Less(FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))), V("a")), Conj(Less(V("a"), FracOf(Num(1), Num(2))), Equal(Call("p1", V("n"), V("a")), Num(0))))))), All(V("a"), FunType(Naturals(), Reals()), ImpliesOf(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Conj(Less(Num(0), Call("a", V("n"))), Conj(Less(Call("a", V("n")), FracOf(Num(1), Num(2))), Equal(Call("p1", V("n"), Call("a", V("n"))), Num(0)))))), Conj(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Less(FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))), Call("a", V("n"))))), Call("Tendsto", V("a"), V("atTop"), Call("nhds", FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))))))))))), "Conjecture 4, page 17: “The cut-off values α_n converge to 1/√5 from above.” Page 16: “We call the roots α_n of the polynomials ₙp₁ the cut-off values for the path graph P_n.” Theorem 19, page 16: “For n − j ≥ 5, ₙp_j(α) has a root between 1/√5 and 1/2.” The first conjunct supplies existence for n ≥ 6. The second quantifies every sequence of roots in (0, 1/2); its first six values are unrestricted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", Conj(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Some(V("a"), Reals(), Conj(Less(FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))), V("a")), Conj(Less(V("a"), FracOf(Num(1), Num(2))), Equal(Call("p1", V("n"), V("a")), Num(0))))))), All(V("a"), FunType(Naturals(), Reals()), ImpliesOf(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Conj(Less(Num(0), Call("a", V("n"))), Conj(Less(Call("a", V("n")), FracOf(Num(1), Num(2))), Equal(Call("p1", V("n"), Call("a", V("n"))), Num(0)))))), Conj(All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), Less(FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))), Call("a", V("n"))))), Call("Tendsto", V("a"), V("atTop"), Call("nhds", FracOf(Num(1), Apply(Qualified("Real", "sqrt"), Num(5))))))))), "Every path size n ≥ 6 has a cut-off in (1/√5, 1/2), and every sequence choosing roots in (0, 1/2) converges to 1/√5 from above. Positive continuants identify the extremal entries; a positive continued fraction makes the crossing strictly increasing, and a geometric-power limit traps every root.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("evans-francis-jones-2025-katz-cutoff-limit"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, string text, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula ImpliesOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula FunType(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
}
