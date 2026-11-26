using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class OneJoinedPathTreesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.";
    private static readonly LibraryNoteRef Question =
        LibraryNoteRef.Create("D5/L/Semigroups/pinzonetal2026onejoinedpaths");
    private static readonly LibraryNoteRef Join =
        LibraryNoteRef.Create("D5/L/Semigroups/pinzonpragelroberts2025graphjoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classification of finite trees formed by one-joining arbitrarily labelled paths.",
        H("One-joined path trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("one-joined-labelled-chain"),
                DeclarationHandle.Create(Owner + "LabeledChain"),
                H("Labelled path blocks and their joins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Join),
                Blocks(
                    Paragraph(Text("The block map partitions the input vertices into k + 1 nonempty fibres. "
                        + "Each fibre has a path-graph isomorphism and a freely chosen bijection from its labels. "
                        + "The only cross-block adjacencies join the largest label of block i to label 1 of block i + 1.")),
                    Paragraph(Text("Lean numbers labels from zero. If p is a block's path coordinate map and l "
                        + "its label map, the relabelling permutation is l inverse composed with p. Conversely a "
                        + "permutation determines l by composing p with its inverse. For a local zero-based label j, "
                        + "add one and the sum of the preceding block orders to obtain its global label. "
                        + "This gives the successive right-label shifts in the cited definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("one-joined-tree-classification"),
                DeclarationHandle.Create(Owner + "oneJoined_iff_spineCut"),
                H("The spine-cut classification"),
                StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(Question),
                Blocks(
                    Paragraph(Text("Let G be a finite simple tree. Its connectedness supplies a vertex. "
                        + "OneJoined means that G admits a labelled chain with each block of order at least m. "
                        + "When b is true it requires at least one join. When b is false it permits one block.")),
                    Paragraph(Text("SpineCut means that some simple path in the input tree carries a set C of edges. "
                        + "Write d for the degree in G and c for incidence in C. For minimum order two, the "
                        + "conditions at every vertex are c ≤ 1 and 1 ≤ d − c ≤ 2. For minimum order one, "
                        + "they are 0 ≤ d − c ≤ 2 and c = 2 implies d = 2. On a simple path there are at most "
                        + "two incidences at any vertex. When b is true, C must be nonempty.")),
                    Paragraph(Text("The two-vertex minimum is the original operand domain. Section 3 discusses "
                        + "the singleton, whose one vertex carries both joining labels. The registered minimum-one "
                        + "extension and the zero-join closures are included in the same equivalence.")),
                    Paragraph(Text("Forward, the actual interblock joins are carried by a simple tree path. "
                        + "After deleting them the residual degree is the intrablock path degree. The original "
                        + "degree is exactly residual degree plus cut incidence. Reverse, order the residual "
                        + "components along the projected path and assign the joining labels in each component."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pinzon-et-al-2026-one-joined-path-trees"), ResolutionKind.Proved)),
            Describe.Lean(DescribeId.Create("one-joined-forward-certificate"),
                DeclarationHandle.Create(Owner + "joinEdges_certificate"),
                H("The actual joins certify a spine cut"),
                StatementSource.FromAuthor(ForwardCertificate()),
                AssessedProvenance.FromRepo(Question),
                Blocks(Paragraph(Text("For a given labelled chain, joinEdges consists of its actual interblock "
                    + "edges. The path from the first block to the last must cross each consecutive boundary. "
                    + "Uniqueness of the crossing edge puts every join on that path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-joined-exact-cut"),
                DeclarationHandle.Create(Owner + "realizes_spine_cut"),
                H("Exact reconstruction of a prescribed cut"),
                StatementSource.FromAuthor(Reconstruction()),
                AssessedProvenance.FromRepo(Question),
                Blocks(
                    Paragraph(Text("For every qualifying C, each block is exactly a component of the graph after "
                        + "deleting C, and the crossing edges are exactly C. The number k counts joins. It is "
                        + "positive exactly when C is nonempty. The residual degree condition is equivalent to "
                        + "the original criterion by the exact degree decomposition.")),
                    Paragraph(Text("Incoming and outgoing endpoints in a block determine labels 1 and the largest "
                        + "label. In a nonsingleton the local incidence test makes the two prescribed vertices "
                        + "distinct whenever both are present. The singleton uses its only label for both."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula For(string id, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(id), type, body);
    private static Formula Some(string id, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(id), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffOf(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula FiniteTree(Formula body)
    {
        Formula v = F.Id("V"), g = F.Id("G");
        return For("V", F.Id("Type"), For("G", Call("SimpleGraph", v),
            Seq(Forall, Sp, OpenBracket, Call("Finite", v), CloseBracket, Comma, Sp,
                Imp(Call("IsTree", g), body))));
    }

    private static Formula Input(Formula body)
    {
        Formula m = F.Id("m");
        return FiniteTree(For("m", F.Id("Nat"),
            Imp(Logic(Eq(m, D(1)), FormulaLogicOperator.Or, Eq(m, D(2))), body)));
    }

    private static Formula PositiveJoins(Formula k, Formula c) =>
        IffOf(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k), Call("Nonempty", c));

    private static Formula MinimumOrder(Formula k, Formula m, Formula l)
    {
        Formula i = F.Id("i");
        var next = new Formula.Binary(k, FormulaBinaryOperator.Add, D(1));
        var order = new Formula.Binary(Call("length", l, i), FormulaBinaryOperator.Add, D(1));
        return For("i", Call("Fin", next),
            new Formula.Relation(m, FormulaRelationOperator.LessThanOrEqual, order));
    }

    private static Formula ForwardCertificate()
    {
        Formula g = F.Id("G"), m = F.Id("m"), k = F.Id("k"), l = F.Id("L"), x = F.Id("x");
        var c = Call("joinEdges", l);
        var conclusion = And(Call("OnSpine", g, c), And(PositiveJoins(k, c),
            For("x", F.Id("V"), Call("ResidualVertexCondition", g, c, m, x))));
        return Disp(FiniteTree(For("k", F.Id("Nat"), For("m", F.Id("Nat"),
            For("L", Call("LabeledChain", g, k), Imp(MinimumOrder(k, m, l), conclusion))))));
    }

    private static Formula Classification()
    {
        Formula g = F.Id("G"), m = F.Id("m"), b = F.Id("b");
        return Disp(Input(For("b", F.Id("Bool"),
            IffOf(Call("OneJoined", g, m, b), Call("SpineCut", g, m, b)))));
    }

    private static Formula Reconstruction()
    {
        Formula v = F.Id("V"), g = F.Id("G"), m = F.Id("m"), c = F.Id("C"), x = F.Id("x");
        Formula k = F.Id("k"), l = F.Id("L");
        var output = Some("k", F.Id("Nat"), Some("L", Call("LabeledChain", g, k),
            And(Eq(Call("joinEdges", l), c), And(PositiveJoins(k, c), MinimumOrder(k, m, l)))));
        return Disp(Input(For("C", Call("Set", Call("Sym2", v)),
            Imp(And(Call("OnSpine", g, c), For("x", v, Call("ResidualVertexCondition", g, c, m, x))),
                output))));
    }
}
