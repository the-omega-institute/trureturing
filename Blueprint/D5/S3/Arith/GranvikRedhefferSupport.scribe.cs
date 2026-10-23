using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GranvikRedhefferSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GranvikRedhefferSupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/granvik2008a145110");
    private static readonly LibraryNoteRef Wilf =
        LibraryNoteRef.Create("D5/L/Factorization/wilf2004redheffer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisor-pair count refutes Granvik's twenty conjectured Redheffer support values.",
        H("Granvik's Redheffer support conjecture"), Blocks(
            Entry("matrix", "B", "The modified Redheffer matrix",
                Disp(Call("B", V("n"), V("i"), V("j"))),
                "Rows and columns are the subtype of natural numbers in the closed interval from one to n. B(n,i,j) is one exactly when j=1 or i divides j, except that the entry (n,n) is zero. Every other entry is zero. This is the Möbius variant identified in A143104 and A008683. The n=8 support array in A145110 uses the transposed display convention.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("support", "contributingPositions", "The union of contributing positions",
                Disp(Call("contributingPositions", V("n"))),
                "A pair (i,j) belongs to this finite set if some actual permutation sigma of all row indices maps i to j and every B(n,k,sigma(k)) equals one. This is the union of positions of nonzero determinant terms, before their signs cancel; it is not the number of such permutations.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("count", "a", "The number of contributing positions",
                Disp(Eqn(Call("a", V("n")), Call("card", Call("contributingPositions", V("n"))))),
                "The count uses the literal permutation-support definition. At n=1 this definition gives zero, whereas the entry lists one; the conjecture being refuted concerns only indices eleven through thirty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("conjecture", "claim", "The twenty published equalities",
                Conjecture(),
                "OEIS A145110 attributes this exact list to Mats Granvik: “a(11) to a(30) are conjectured to be 11, 23, 13, 18, 19, 25, 17, 29, 19, 30, 26, 26, 23, 45, 27, 30, 32, 39, 29, 48.” The proposition claim is closed and conjoins all twenty equalities in this order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "Refutation by the general support formula",
                Disp(new Formula.Not(V("claim"))),
                "For every n at least two, the proof establishes a(n)=n−1+sum over d dividing n of (card(d.divisors)−1). The contributing positions are exactly the n−2 interior diagonal positions, the closing position (n,1), and the strict-divisibility positions (i,j) with i<j and i dividing j dividing n. An admissible permutation preserves the divisor set of n; a finite sum of nonnegative coordinate increments forces every nondivisor to be fixed. Each strict-divisibility edge is realized by a cycle through 1,i,j,n, omitting repeated endpoints, and every remaining index is fixed. Disjoint counting by the second coordinate gives the formula. This support-union identity is derived here; Wilf's Theorem 1 concerns the contributing permutations of the standard Redheffer matrix. At n=20 the divisor summands are 0,1,2,1,3,5, so a(20)=19+12=31, contradicting the conjectured value 30. The theorem has type Not claim. No bound on the Mertens function follows from this support count.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Wilf),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a145110-granvik-redheffer-support-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string text, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(text))),
            role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Conjecture()
    {
        int[] values = [11, 23, 13, 18, 19, 25, 17, 29, 19, 30,
            26, 26, 23, 45, 27, 30, 32, 39, 29, 48];
        Formula body = Eqn(Call("a", D(30)), D(values[19]));
        for (int k = 18; k >= 0; --k)
            body = new Formula.Logic(Eqn(Call("a", D(k + 11)), D(values[k])),
                FormulaLogicOperator.And, body);
        return Disp(Eqn(V("claim"), body));
    }
}
