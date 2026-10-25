using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class ReverseLevelOrderTreeLabelingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/GraphInvariants/leskovjanovamista2025gaussiangme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A labeling that decreases with distance from a tree's root gives exactly one nonzero entry in every column tail before the last column.",
        H("Reverse level order labeling of a tree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The column-tail property"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let g be a tree on Fin n, let r be any root, and let l be a bijection from its vertices to Fin n. "
                    + "The order on the domain of StrictAnti is the preorder lifted along the distance from r; "
                    + "the order on its codomain is the usual order on Fin n. Thus smaller distance requires a larger label, "
                    + "with no restriction on the relative labels within a level. The explicit DFunLike.coe applications "
                    + "regard the bijections as functions, and Fin.val i is the natural-number value of i. "
                    + "For each i with Fin.val i + 1 < n, exactly one row j larger than i has a nonzero adjacency entry "
                    + "at the vertices with labels j and i. The adjacency matrix takes values in the natural numbers. "
                    + "Section 4.1.3 of the source, Quantum-accepted.tex lines 828–835, chooses a central root and labels "
                    + "the levels in decreasing order; lines 837–839 conjecture this column-tail property. "
                    + "Here the labels 0 through n minus one correspond to the source's labels 1 through n, "
                    + "and the statement permits every root and every order within a level."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Exactly one nonzero entry in each column tail"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First fix a vertex v distinct from r and take a shortest walk p from v to r. "
                        + "Write its first edge as v to w and its remaining walk as q from w to r. "
                        + "The distance from r to w is at most the length of q, while the length of q plus one "
                        + "equals the distance from r to v. Along an edge of a tree the two distances from r differ "
                        + "by exactly one. These facts force the distance from r to w plus one to equal the distance from r to v.")),
                    Paragraph(Text(
                        "If u is another neighbor of v whose distance from r plus one equals the distance from r to v, "
                        + "take a shortest walk s from u to r. Prepending the edge from v to u makes a walk whose length "
                        + "equals the distance from v to r. It is therefore a path, as is p. A tree has a unique path "
                        + "between these endpoints, so the two paths agree. Their vertices at position one are u and w, "
                        + "which must be equal. Thus each vertex distinct from r has a unique neighbor one level nearer r.")),
                    Paragraph(Text(
                        "Next consider adjacent vertices v and w. Their levels differ by one. If l(v) < l(w), "
                        + "the alternative that w is one level farther from r would give l(w) < l(v) by strict antitonicity, "
                        + "a contradiction. Hence w is one level nearer r. Conversely, if w is one level nearer r, "
                        + "strict antitonicity gives l(v) < l(w). Larger labels among neighbors therefore characterize the parent.")),
                    Paragraph(Text(
                        "Now fix i with Fin.val i + 1 < n. The vertex with label i cannot be r. "
                        + "Indeed, suppose it were r and let j be the element of Fin n with value Fin.val i + 1. "
                        + "Injectivity of the inverse labeling ensures that the vertex with label j differs from r. "
                        + "Its distance from r is positive, whereas the distance from r to itself is zero. "
                        + "Strict antitonicity would give j < i, contradicting the choice of j.")),
                    Paragraph(Text(
                        "For the vertex with label i, take its unique parent w and set j = l(w). "
                        + "The label comparison gives i < j, and symmetry of adjacency makes the matrix entry in row j "
                        + "and column i equal to one. For any row j larger than i with a nonzero entry, the corresponding "
                        + "vertex must be adjacent to the vertex with label i, since a nonadjacent entry is zero. "
                        + "The label comparison makes that vertex a parent, so uniqueness identifies it with w. "
                        + "Applying l identifies its row label with l(w). This proves existence and uniqueness for every required column."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("leskovjanova-mista-2025-reverse-level-order-tree-labeling"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        Formula inverse = At(Qualified("DFunLike", "coe"), At(Qualified("Equiv", "symm"), X("l")));
        Formula entry = At(Qualified("SimpleGraph", "adjMatrix"), Naturals(), X("g"),
            At(inverse, X("j")), At(inverse, X("i")));
        Formula tail = Seq(Exists, Bang, Sp, Typed(X("j"), FinN()), Comma, Sp,
            Parenthesized(Conjunction(Less(X("i"), X("j")), NotEqual(entry, Typed(D(0), Naturals())))));
        Formula indexBound = Less(
            Add(At(Qualified("Fin", "val"), X("i")), Typed(D(1), Naturals())), X("n"));
        Formula orders = Seq(
            At(Qualified("Preorder", "lift"), At(Qualified("SimpleGraph", "dist"), X("g"), X("r"))),
            Comma, Sp, Qualified("inferInstance"));
        Formula decreasing = At(new Formula.Subscript(Qualified("StrictAnti"), orders),
            At(Qualified("DFunLike", "coe"), X("l")));
        Formula labels = All("r", FinN(), All("l", At(Qualified("Equiv"), FinN(), FinN()),
            Arrow(decreasing, All("i", FinN(), Arrow(indexBound, tail)))));
        Formula trees = Arrow(At(Qualified("SimpleGraph", "IsTree"), X("g")), labels);
        Formula decidable = Seq(OpenBracket,
            At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("g"))),
            CloseBracket, Comma, Sp, Parenthesized(trees));
        return All("n", Naturals(), All("g", At(Qualified("SimpleGraph"), FinN()), decidable));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Combinatorics", "SpectralGraph",
        "ReverseLevelOrderTreeLabeling", name);
    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula FinN() => At(Qualified("Fin"), X("n"));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
