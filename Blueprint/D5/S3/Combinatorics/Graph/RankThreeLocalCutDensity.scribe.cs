using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class RankThreeLocalCutDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary cut bounds on indexed support traces yield a strong seven-coloring at rank three and a weighted density bound without a rank restriction.",
        H("Weighted Density from Local Trace Cuts"),
        Blocks(
            Paragraph(Text(
                "Let V be a finite vertex set, I a finite set of owner indices, and A(i) a finite "
                + "support for each index. Different indices may carry the same support and are counted "
                + "separately. TraceCap means that for every S contained in V and every L contained in S, "
                + "at most |S| indexed traces A(i) intersected with S meet both L and S minus L. "
                + "The condition counts each crossing index once, regardless of its support size. "
                + "It is imposed on all traces, including those of supports not contained in S.")),
            Describe.Lean(DescribeId.Create("strong-seven-coloring"),
                DeclarationHandle.Create(Prefix + "strong_seven_coloring"),
                H("Strong Seven-Coloring for Rank Three"),
                StatementSource.FromAuthor(ColoringFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose every indexed support has at most three vertices and TraceCap holds. "
                    + "There is a map from the ambient vertex type to Fin(7) assigning different colors "
                    + "to every two distinct vertices of a common support that both lie in V. "
                    + "Support vertices outside V are allowed and impose no coloring condition. "
                    + "For a trace of size two or three, four times its crossing-cut count is its size "
                    + "times 2 to the power |S|. Traces of size zero or one contribute zero. "
                    + "The empty cut makes the resulting incidence bound strict on every nonempty S: "
                    + "the total incidence of nontrivial traces is less than 4|S|. Thus some vertex "
                    + "belongs to at most three nontrivial indexed traces and has at most six distinct "
                    + "neighbors. Deleting it, coloring inductively, and restoring a missing color "
                    + "constructs the asserted coloring."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a strong seven-coloring, omit one color and divide the remaining six colors "
                + "into an ordered choice of three left colors and three right colors. There are "
                + "7 times 20 such cuts. A pair of different colors crosses 60 of them, a triple "
                + "of different colors crosses 108, and each vertex remains available in 120. "
                + "These counts follow from fixed-size subset counts using binomial coefficients. "
                + "Apply TraceCap on each available vertex set and double count to obtain "
                + "60 times the number of pairs plus 108 times the number of triples at most 120|V|.")),
            Describe.Lean(DescribeId.Create("weighted-density"),
                DeclarationHandle.Create(Prefix + "local_cut_density"),
                H("The Weighted Bound for Arbitrary Support Sizes"),
                StatementSource.FromAuthor(DensityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume every indexed support is contained in V and TraceCap holds. Write n2 "
                    + "for the number of indices with exactly two support vertices and n3plus for "
                    + "the number with at least three. Then 5 n2 + 9 n3plus is at most 10|V|. "
                    + "There is no upper bound on the original support sizes. Choose a three-element "
                    + "subset of every support of size at least three, leaving smaller supports "
                    + "unchanged. Shrinking supports preserves TraceCap because every crossing "
                    + "of a smaller trace is also a crossing of the original trace. Apply the rank-three "
                    + "coloring and cut count to the shrunken supports. Empty and singleton supports "
                    + "are permitted and contribute zero. Applying this finite combinatorial result "
                    + "to a congruence system requires a separate proof of its hereditary trace capacity."))),
                DescribeRole.Theorem))));

    private static Formula ColoringFormula() => Disp(All("V", Call("Finset", F.Id("Vertex")),
        All("I", Call("Finset", F.Id("Owner")), All("A", Call("Function", F.Id("Owner"), Call("Finset", F.Id("Vertex"))),
            Implies(And(Call("SupportRankAtMost", F.Id("I"), F.Id("A"), D(3)),
                Call("TraceCap", F.Id("V"), F.Id("I"), F.Id("A"))),
                Exists("c", Call("Function", F.Id("Vertex"), Call("Fin", D(7))),
                    Call("StrongOnSupportVerticesIn", F.Id("V"), F.Id("I"), F.Id("A"), F.Id("c"))))))));

    private static Formula DensityFormula() => Disp(All("V", Call("Finset", F.Id("Vertex")),
        All("I", Call("Finset", F.Id("Owner")), All("A", Call("Function", F.Id("Owner"), Call("Finset", F.Id("Vertex"))),
            Implies(And(Call("SupportsContainedIn", F.Id("V"), F.Id("I"), F.Id("A")),
                Call("TraceCap", F.Id("V"), F.Id("I"), F.Id("A"))),
                Le(Add(Mul(D(5), Call("CountSupportSize", F.Id("I"), F.Id("A"), D(2))),
                    Mul(D(9), Call("CountSupportSizeAtLeast", F.Id("I"), F.Id("A"), D(3)))),
                    Mul(D(1, 0), Call("card", F.Id("V")))))))));

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula l, Formula r) =>
        new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
}
