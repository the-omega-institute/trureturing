using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.KatzCutoff;

internal sealed class ReductionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Recurrence/KatzCutoff/Reduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/evansfrancisjones2025katz");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuants, path entries and Katz cut-offs.",
        H("Reduction"),
        Blocks(
            Paragraph(Text("Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.")),
            Node("katz", All(V("n"), Naturals(), All(Alpha, Reals(), Equal(Call("katz", V("n"), Alpha), Subtract(Inv(Subtract(Num(1), Seq(Alpha, Sp, Cdot, Sp, Apply(DotOf(Apply(Qualified("SimpleGraph", "pathGraph"), V("n")), "adjMatrix"), Reals())))), Num(1))))), "Definition 1, page 2: “Let G be a simple graph with adjacency matrix A, and let 0 < α < 1/ρ(A). Then the Katz matrix of G at α is given by K_G(α) = αA + α²A² + α³A³ + ⋯ = ∑_{t=1}^∞ αᵗAᵗ = (I − αA)⁻¹ − I and the Katz similarity index at α between vertices i and j of G is given by K_G(α)_{i,j}.” Here G is SimpleGraph.pathGraph n, on Fin n, and the inverse is the matrix inverse.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("katzEntry", All(V("n"), Naturals(), All(Alpha, Reals(), All(V("i"), Naturals(), All(V("j"), Naturals(), Equal(Call("katzEntry", V("n"), Alpha, V("i"), V("j")), IfProof(V("h"), Conj(Less(V("i"), V("n")), Less(V("j"), V("n"))), Apply(Call("katz", V("n"), Alpha), PairOf(V("i"), DotOf(V("h"), "1")), PairOf(V("j"), DotOf(V("h"), "2"))), Num(0))))))), "Definition 1, page 2: “Let G be a simple graph with adjacency matrix A, and let 0 < α < 1/ρ(A). Then the Katz matrix of G at α is given by K_G(α) = αA + α²A² + α³A³ + ⋯ = ∑_{t=1}^∞ αᵗAᵗ = (I − αA)⁻¹ − I and the Katz similarity index at α between vertices i and j of G is given by K_G(α)_{i,j}.” The indices here start at zero; an out-of-range index gives zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("p1", All(V("n"), Naturals(), All(Alpha, Reals(), Equal(Call("p1", V("n"), Alpha), Subtract(Apply(V("iInf"), LambdaOf(V("i"), Call("Fin", Subtract(V("n"), Num(1))), Call("katzEntry", V("n"), Alpha, Call("val", V("i")), Add(Call("val", V("i")), Num(1))))), Apply(V("iSup"), LambdaOf(V("i"), Call("Fin", Subtract(V("n"), Num(2))), Call("katzEntry", V("n"), Alpha, Call("val", V("i")), Add(Call("val", V("i")), Num(2))))))))), "Section 4.2, page 13: “Consider the polynomial ₙp_j(α) = min_i K_{P_n}(α)_{i,i+j} − max_i K_{P_n}(α)_{i,i+j+1}.” The display specializes j to one and uses exactly the ranges on which both vertices exist.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("p1_reduction", All(V("n"), Naturals(), ImpliesOf(LessEq(Num(6), V("n")), All(Alpha, Reals(), ImpliesOf(Less(Num(0), Alpha), ImpliesOf(Less(Alpha, FracOf(Num(1), Num(2))), Equal(Call("p1", V("n"), Alpha), Multiply(FracOf(Multiply(Alpha, Apply(Apply(Qualified("LinearRecurrence", "mkSol"), Apply(Qualified("LinearRecurrence", "mk"), Num(2), Seq(Bang, OpenBracket, Seq(Minus, Pow(Alpha, Num(2))), Comma, Num(1), CloseBracket)), Seq(Bang, OpenBracket, Num(1), Comma, Num(1), CloseBracket)), Subtract(V("n"), Num(2)))), Apply(Apply(Qualified("LinearRecurrence", "mkSol"), Apply(Qualified("LinearRecurrence", "mk"), Num(2), Seq(Bang, OpenBracket, Seq(Minus, Pow(Alpha, Num(2))), Comma, Num(1), CloseBracket)), Seq(Bang, OpenBracket, Num(1), Comma, Num(1), CloseBracket)), V("n"))), Parenthesized(Subtract(Num(1), Call("RAB", Alpha, NatDiv(V("n"), Num(2)), NatDiv(Subtract(V("n"), Num(1)), Num(2)))))))))))), "Proposition 15, page 14, reduces the comparison of the distance-one and distance-two Katz entries to the scalar ratio RAB.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, Formula formula, string text, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(Parenthesized(value), power);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula ImpliesOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula LambdaOf(Formula name, Formula type, Formula body) => Parenthesized(Seq(V("fun"), Sp, name, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula DotOf(Formula owner, string name) => Seq(owner, Dot, name == "1" ? Num(1) : name == "2" ? Num(2) : V(name));
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula NatDiv(Formula a, Formula b) => Apply(Qualified("Nat", "div"), a, b);
    private static Formula PairOf(Formula a, Formula b) => Seq(Langle, Sp, a, Comma, Sp, b, Sp, Rangle);
    private static Formula IfProof(Formula h, Formula p, Formula yes, Formula no) => Parenthesized(Seq(V("if"), Sp, h, Colon, Sp, Parenthesized(p), Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no));
    private static Formula Inv(Formula a) => Pow(a, Seq(Minus, Num(1)));
}
