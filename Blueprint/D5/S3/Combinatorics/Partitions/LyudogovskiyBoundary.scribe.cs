using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class LyudogovskiyBoundaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/lyudogovskiy2026simplex");

    public DocumentDefinition Create()
    {
        var r = FormulaDsl.Id("r");
        var n = FormulaDsl.Id("n");
        var p = FormulaDsl.Id("p");
        var q = FormulaDsl.Id("q");
        var partition = Call("Partition", n);
        var next = new Formula.Binary(r, FormulaBinaryOperator.Add, D(1));
        var edge = Call("Adj", Call("graph", n), p, q);
        var endpoints = And(edge,
            And(Eq(Call("localDimension", p), r), Eq(Call("localDimension", q), next)));
        var admissible = And(Lt(D(0), n), Bind(FormulaQuantifier.Exists, "p", partition,
            Bind(FormulaQuantifier.Exists, "q", partition, endpoints)));
        var sizes = Seq(OpenBrace, n, Colon, FormulaDsl.Id("Nat"), Mid, admissible, CloseBrace);
        var size = new Formula.Binary(Call("triangular", next), FormulaBinaryOperator.Add, D(1));
        var statement = Bind(FormulaQuantifier.ForAll, "r", FormulaDsl.Id("Nat"),
            new Formula.Logic(Le(D(1), r), FormulaLogicOperator.Implies, Call("IsLeast", sizes, size)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The first transfer boundary between consecutive exact local clique layers.",
            H("Boundary thresholds in the integer-partition graph"), Blocks(
                Describe.Lean(DescribeId.Create("lyudogovskiy-boundary-result"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result"),
                    H("The first boundary occurs at the threshold of the higher layer"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
                    Blocks(
                        Paragraph(Text("Problem 6.3 in the source asks when consecutive exact layers first share a transfer edge. Adj(graph(n), p, q) is literal unit-transfer adjacency between native partitions of n. IsLeast includes attainment and comparison with every positive admissible size. The higher-layer threshold formula identifies the displayed size with the threshold of layer r+1.")),
                        Paragraph(Text("Delete the last singleton from the top-row extension of the staircase of rank r+1. The common diagram has r+1 selected addable corners. Their insertions give a clique of size r+1. One endpoint is a first-occurrence partition in layer r+1. The other lacks a required staircase cell, and the clique lower bound and the maximum upper bound give dimension exactly r.")),
                        Paragraph(Text("For r=0 the set is empty. Each edge forms a clique of size two, so both endpoints have local dimension at least one. The source defines its boundary threshold only when the defining set is nonempty."))),
                    DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("lyudogovskiy-2026-boundary-threshold"), ResolutionKind.Proved)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(FormulaDsl.Id(name))), [.. args]);
    private static Formula Bind(FormulaQuantifier q, string name, Formula domain, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Le(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula Lt(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.LessThan, rhs);
}
