using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class BarrettBalancedLaplacianSpreadGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/barrett2022laplacianspread");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A balanced loopless unweighted digraph has no Laplacian spread strictly between zero and one.",
        H("The balanced-digraph Laplacian-spread gap"), Blocks(
            Node("claim", "Conjecture 14", new Formula.Logic(Call("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                "Conjecture 14, page 15: \"There is no balanced digraph that satisfies 0<sp(Γ)<1.\" Section 6 states: \"Note that all conjectures are made for unweighted digraphs.\" The quantifiers cover every order n≥2 and every loopless directed relation on Fin n. Opposite arcs are allowed. Balanced and spread are the shared directed-degree and quadratic-extremum definitions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Conjecture 14 is true", ClaimBody(),
                "Projected coordinate vectors give Rayleigh values ndᵢ/(n−1). Integral degrees therefore coincide whenever the spread is at most one. The symmetric adjacency matrix has entries 0, 1, or 2. A width below one reduces it, or its complement, to an even-regular simple graph. At interior degrees the centered Frobenius estimate contradicts that width. The matching endpoint gives Rayleigh values −1 and 1, and the empty and complete endpoints have scalar restrictions and zero spread. This proves the entire quantified gap assertion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimBody()
    {
        Formula g = V("G"), n = V("n"), i = V("i");
        Formula spread = Shared("spread", g);
        Formula gap = new Formula.Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, spread),
            FormulaLogicOperator.And, new Formula.Relation(spread, FormulaRelationOperator.LessThan, D(1)));
        Formula loopless = All("i", Call("Fin", n), Notn(App(Q("Digraph", "Adj"), g, i, i)));
        return All("n", Naturals(), Imp(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n),
            All("G", Call("Digraph", Call("Fin", n)), Imp(loopless, Imp(Shared("Balanced", g), Notn(gap))))));
    }

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(DescribeId.Create("bce14-" + selector),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Shared(string name, params Formula[] args) => App(Q("BarrettLaplacianSpreadSlopeRefutation", name), args);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Notn(Formula body) => Seq(Neg, Sp, Parenthesized(body));
}
