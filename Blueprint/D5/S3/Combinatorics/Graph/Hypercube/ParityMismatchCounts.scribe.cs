using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class ParityMismatchCountsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var a = F.Id("a");
        var positive = Seq(D(0), Sp, Lt, Sp, k);
        return Disp(All("n", F.Id("Nat"), All("k", F.Id("Nat"),
            new Formula.Logic(positive, FormulaLogicOperator.Implies,
                Seq(Open, All("a", Call("CountVectors", n),
                    new Formula.Logic(Call("Realized", n, k, a),
                        FormulaLogicOperator.Iff, Call("EvenCuts", n, k, a))), Close)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The even-word inequalities classify integer coordinate mismatch counts.",
        H("Exact mismatch vectors for parity couplings"),
        Blocks(Describe.Lean(DescribeId.Create("parity-coupling-exact-mismatch-counts"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts.exact_integer_parity_mismatch_counts"),
            H("Realizing prescribed coordinate disagreement counts"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("CountVectors(n) consists of natural-valued functions on Fin(n+2). " +
                    "Realized(n,k,a) means one natural count matrix between the even and odd profile " +
                    "classes has every row and column sum equal to k, with total coordinate " +
                    "disagreement count equal to twice a(i) at every i.")),
                Paragraph(Text("Let M be k times 2 to the power n. EvenCuts(n,k,a) means every a(i) " +
                    "is at most M and every even binary word e satisfies the following inequality. " +
                    "Sum a(i) over the zero coordinates of e and M minus a(i) over its one coordinates. " +
                    "The result is at least M.")),
                Paragraph(Text("For necessity, the two profiles in a used pair differ by an odd word, " +
                    "which has distance at least one from every even word. Summing the distances with " +
                    "the matrix weights gives the inequalities.")),
                Paragraph(Text("For sufficiency, fix the column sums of a binary table with twice M " +
                    "rows and minimize the number of even rows. Two distinct even rows allow a " +
                    "single-column swap that makes both odd. If an odd row differs from the common " +
                    "even row at more than one coordinate, one swap produces a different even row " +
                    "and reduces to that case. The only remaining positive minimum violates an " +
                    "even-word inequality. Apply Hall's prescribed-difference theorem to the odd " +
                    "rows using the product of the profile tail group and the cyclic group of copy " +
                    "indices. Summing the resulting labelled pairs over the copy indices gives the matrix."))),
            DescribeRole.Theorem))));
}
