using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Saturation;

internal sealed class MatchingConeLeafUniversalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A leaf's neighbor is universal in every finite maximal H-free graph with at most order plus five edges, where H is the cone over three disjoint edges and an isolated vertex.",
        H("Leaf Neighbors in Sparse Matching-Cone-Saturated Graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("matching-cone"),
                DeclarationHandle.Create(Prefix + "H"), H("The Eight-Vertex Matching Cone"),
                StatementSource.FromAuthor(Disp(Equal(F.Id("H"),
                    Call("Join", Call("K", D(1)),
                        Call("DisjointUnion", Call("ThreeCopies", Call("K", D(2))),
                            Call("K", D(1))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is Unit + (Unit + (Fin 3 x Bool)). Its left unit is the center, "
                    + "its right-left unit is the pendant, and (i,false),(i,true) are the endpoints "
                    + "of matching edge i. The seven center spokes and the three matching edges "
                    + "are precisely its ten required edges. SimpleGraph.Copy is an injective "
                    + "adjacency-preserving map; additional host edges are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("leaf-neighbor-universal"),
                DeclarationHandle.Create(Prefix + "leaf_neighbor_isUniversal"),
                H("The Neighbor of a Leaf Is Universal"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let B be the vertices other than v not adjacent to v. For x in B, the "
                    + "leaf u is distinct from x and ux is missing. Maximal H-freeness supplies "
                    + "a copy after ux is added. A required edge must use ux. In the enlarged "
                    + "graph u lies in no triangle: its only possible neighbors are v and x, "
                    + "which are nonadjacent. Every H role except the pendant lies in a triangle, "
                    + "so u is the pendant and x the center. All six endpoint spokes and all "
                    + "three matching edges are old. An old neighbor of x outside those six "
                    + "endpoints could replace the pendant and construct an old forbidden copy. "
                    + "Consequently each x in B has degree six.")),
                    Paragraph(Text(
                    "Delete the edges incident to v and call the resulting graph D. Write "
                    + "k = |B| and r = |E(D)|. The original edge bound gives r <= k+6. The "
                    + "degree sum gives 6k <= 2r, hence k <= 3. If k >= 2, the incidence "
                    + "sets of two distinct B vertices each have six edges and overlap in at "
                    + "most one edge, giving 11 <= r <= 9. If k = 1, its six spokes and three "
                    + "distinct matching edges give 9 <= r <= 7. Thus B is empty. All counts "
                    + "refer to this same host graph and its actual edge deletion.")),
                    Paragraph(Text(
                    "The quantifiers range over arbitrary finite host types. No order cutoff, "
                    + "connectivity, existence of a leaf, exact saturation value, or resolution "
                    + "of a broader saturation problem is asserted. This structural implication "
                    + "is a repository derivation using Mathlib's copy, maximality, leaf "
                    + "uniqueness, incidence and degree-sum interfaces."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula g = F.Id("G"), v = F.Id("v"), u = F.Id("u");
        Formula hypotheses = And(Call("Maximal", Call("Free", F.Id("H")), g),
            And(new Formula.Relation(Call("card", Call("edgeFinset", g)),
                    FormulaRelationOperator.LessThanOrEqual,
                    Add(Call("FintypeCard", F.Id("V")), D(5))),
                And(Equal(Call("degree", g, u), D(1)), Call("Adj", g, u, v))));
        return Disp(All("V", Call("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
            All("G", Call("SimpleGraph", F.Id("V")), Seq(
                OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket, Sp,
                All("u", F.Id("V"), All("v", F.Id("V"),
                    Implies(hypotheses, Call("IsUniversal", g, v)))))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
