using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.TransientTrees;

internal sealed class RootedVertexReconstructionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal branch codes reconstruct actual rooted vertices and internal child edges.",
        H("Rooted Vertex Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-descendants"),
                DeclarationHandle.Create(Owner + "Descendant"),
                H("Original descendant vertices"),
                StatementSource.FromAuthor(DescendantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is a subtype of the original state space. The root is included "
                    + "by the reflexive path. TransientChild is the existing nonperiodic-child "
                    + "relation, directed toward the parent; val denotes subtype projection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rooted-vertex-equivalence"),
                DeclarationHandle.Create(Owner + "RootedVertexEquiv"),
                H("Root-preserving vertex equivalence"),
                StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed equiv, rootEq, and childIff denote the Lean fields equiv, "
                    + "root_eq, and child_iff. "
                    + "The equivalence includes both inverse laws. This definition requires "
                    + "no finiteness instances; finiteness is used by the reconstruction theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("descendant-partition"),
                DeclarationHandle.Create(Owner + "descendantPartition"),
                H("Root and disjoint child subtrees"),
                StatementSource.FromAuthor(PartitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Option value none denotes the root. A some value carries an actual "
                    + "immediate child and an original vertex below that child. Deterministic "
                    + "parents make paths comparable; well-foundedness excludes a return to "
                    + "the root and forces the immediate child to be unique. The resulting "
                    + "bijection supplies the inverse used in reconstruction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("branch-code-reconstruction"),
                DeclarationHandle.Create(Owner + "rooted_vertex_equiv_of_branch_code_eq"),
                H("Equal branch codes reconstruct rooted vertices"),
                StatementSource.FromAuthor(ReconstructionFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RootedVertexEquiv stores precisely the displayed equivalence, root equality, "
                    + "and child-relation iff in its equiv, root_eq, and child_iff fields. "
                    + "The theorem asserts that this structure is nonempty. The two universes "
                    + "are independent, and no equality of ambient cardinalities is assumed.")),
                    Paragraph(Text(
                    "Equality of encoded child multisets matches occurrences with their full "
                    + "multiplicities. Well-founded recursion constructs the child equivalences. "
                    + "The actual partition inverse, the dependent sum of those equivalences, "
                    + "and the target partition form the vertex equivalence. The edge proof "
                    + "includes both internal subtree edges and edges from child roots to the root.")),
                    Paragraph(Text(
                    "An arbitrary root may be transient, and its outgoing update may leave this "
                    + "carrier. The result asserts only the displayed internal child relation. "
                    + "The converse classification, cycle and component gluing, cardinal-depth "
                    + "saturation, and the compatible-family inverse are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recursive-matching-reconstruction"),
                DeclarationHandle.Create(Owner + "rooted_vertex_equiv_of_recursive_isomorphism"),
                H("Recursive matching reconstructs the same vertices"),
                StatementSource.FromAuthor(ReconstructionFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing recursive Multiset.Rel predicate gives equal branch codes by "
                    + "the frozen classifier, so the same reconstruction applies."))),
                DescribeRole.Theorem))));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula TypeAt(string level) => Seq(Name("Type"), Underscore, Grp(F.Id(level)));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Root(Formula r) => Seq(Langle, Sp, r, Comma, Sp, Name("refl"), Rangle);
    private static Formula Desc(Formula f, Formula r) => Call("Descendant", f, r);
    private static Formula Child(Formula f, Formula x, Formula y) => Call("TransientChild", f, x, y);
    private static Formula Row => Seq(RowBreak, Grp());
    private static Formula Gather(params Formula[] content) =>
        Disp(Seq(Begin, Grp(F.Id("gathered")), Seq(content), End, Grp(F.Id("gathered"))));

    private static Formula DescendantFormula()
    {
        Formula y = F.Id("Y"), f = F.Id("f"), r = F.Id("r"), x = F.Id("x");
        return Gather(
            F.Id("u"), Sp, Name("universe"), Comma, Sp,
            Forall, Sp, y, Colon, Sp, TypeAt("u"), Comma, Sp,
            f, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp, r, Colon, Sp, y, Comma, Row,
            Desc(f, r), Colon, Eq, Sp, OpenBrace, Sp, x, Colon, Sp, y, Sp, Mid, Sp,
            Call("ReflTransGen", Call("TransientChild", f), x, r), Sp, CloseBrace);
    }

    private static Formula EquivalenceFormula()
    {
        Formula y = F.Id("Y"), z = F.Id("Z"), f = F.Id("f"), g = F.Id("g");
        Formula r = F.Id("r"), s = F.Id("s"), a = F.Id("a"), b = F.Id("b");
        return Gather(
            F.Id("u"), Comma, Sp, F.Id("v"), Sp, Name("universes"), Comma, Row,
            Forall, Sp, y, Colon, Sp, TypeAt("u"), Comma, Sp,
            z, Colon, Sp, TypeAt("v"), Comma, Row,
            Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            g, Colon, Sp, z, Sp, To, Sp, z, Comma, Sp,
            r, Colon, Sp, y, Comma, Sp, s, Colon, Sp, z, Comma, Row,
            Name("RootedVertexEquiv"), Open, f, Comma, Sp, g, Comma, Sp, r, Comma, Sp, s,
            Close, Sp, Name("fields"), Colon, Row,
            Name("equiv"), Colon, Sp, Call("Equiv", Desc(f, r), Desc(g, s)), Comma, Row,
            Name("rootEq"), Colon, Sp, Call("equiv", Root(r)), Eq, Root(s), Comma, Row,
            Name("childIff"), Colon, Sp,
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, Desc(f, r), Comma, Sp,
            Child(f, Val(a), Val(b)), Sp, Iff, Sp,
            Child(g, Val(Call("equiv", a)), Val(Call("equiv", b))));
    }

    private static Formula PartitionFormula()
    {
        Formula y = F.Id("Y"), f = F.Id("f"), r = F.Id("r"), c = F.Id("c"), x = F.Id("x");
        Formula p = F.Id("p"), a = F.Id("a");
        Formula children = Seq(OpenBrace, Sp, c, Colon, Sp, y, Sp, Mid, Sp,
            Child(f, c, r), Sp, CloseBrace);
        Formula pieces = Call("Option", Seq(Name("Sigma"), Underscore,
            Grp(c, Colon, Sp, children), Sp, Desc(f, Val(c))));
        Formula applyInverse = Call("inverse", p, x);
        return Gather(
            F.Id("u"), Sp, Name("universe"), Comma, Sp,
            Forall, Sp, y, Colon, Sp, TypeAt("u"), Comma, Sp,
            OpenBracket, Call("Finite", y), CloseBracket, Comma, Row,
            Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            r, Colon, Sp, y, Comma, Row,
            p, Colon, Eq, Sp, Call("descendantPartition", f, r), Colon, Sp,
            Call("Equiv", pieces, Desc(f, r)), Comma, Row,
            Call("p", Name("none")), Eq, Root(r), Comma, Row,
            Forall, Sp, c, Colon, Sp, children, Comma, Sp, x, Colon, Sp,
            Desc(f, Val(c)), Comma, Sp,
            Call("val", Call("p", Call("some", Seq(Langle, Sp, c, Comma, Sp, x, Rangle)))),
            Eq, Val(x), Comma, Row,
            Forall, Sp, a, Colon, Sp, pieces, Comma, Sp,
            Call("inverse", p, Call("p", a)), Eq, a, Comma, Row,
            Forall, Sp, x, Colon, Sp, Desc(f, r), Comma, Sp,
            Call("p", applyInverse), Eq, x);
    }

    private static Formula ReconstructionFormula(bool recursive)
    {
        Formula y = F.Id("Y"), z = F.Id("Z"), f = F.Id("f"), g = F.Id("g");
        Formula r = F.Id("r"), s = F.Id("s"), e = F.Id("e"), a = F.Id("a"), b = F.Id("b");
        Formula premise = recursive
            ? Call("RootedTransientTreeIsomorphic", f, g, r, s)
            : Seq(Call("branchCode", f, r), Eq, Call("branchCode", g, s));
        return Gather(
            F.Id("u"), Comma, Sp, F.Id("v"), Sp, Name("universes"), Comma, Row,
            Forall, Sp, y, Colon, Sp, TypeAt("u"), Comma, Sp,
            z, Colon, Sp, TypeAt("v"), Comma, Row,
            OpenBracket, Call("Fintype", y), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", z), CloseBracket, Comma, Row,
            Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            g, Colon, Sp, z, Sp, To, Sp, z, Comma, Sp,
            r, Colon, Sp, y, Comma, Sp, s, Colon, Sp, z, Comma, Row,
            premise, Sp, Implies, Row,
            Exists, Sp, e, Colon, Sp, Call("Equiv", Desc(f, r), Desc(g, s)), Comma, Row,
            Call("e", Root(r)), Eq, Root(s), Sp, Land, Row,
            Open, Forall, Sp, a, Comma, Sp, b, Colon, Sp, Desc(f, r), Comma, Sp,
            Child(f, Val(a), Val(b)), Sp, Iff, Sp,
            Child(g, Val(Call("e", a)), Val(Call("e", b))), Close);
    }
}
