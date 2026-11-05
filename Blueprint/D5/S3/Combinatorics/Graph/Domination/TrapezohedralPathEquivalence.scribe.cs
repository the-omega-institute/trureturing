using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralPathEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete labelled-subset count is obtained through inverse ordered-path maps.",
        H("From actual graph subsets to actual path subsets"), Blocks(
            Paragraph(Text("Fix n>=3 and the deleted cyclic edge j. The ordered path map is t -> t+(j+1) in Fin n. It sends the first path label to j+1 and the last to j. Every path edge is exactly a remaining cyclic edge, in either orientation. The native Mathlib vertex-cover/complement theorem is reused; minimality is transported by order reversal of inclusion. An endpoint belongs to the cover exactly when the corresponding endpoint is absent from its independent complement.")),
            Describe.Lean(DescribeId.Create("ordered-equivalence"), DeclarationHandle.Create(Prefix + "coverPathEquiv"),
                H("Both inverse label maps"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each n>=3, CoverData n is equivalent to Fin n times the subtype of actual finite subsets in restrictedFamily n. Encode selects exactly the natural labels t.val whose ordered cyclic label is outside C. Decode declares i in C exactly when the value of the inverse ordered label is absent from I. The two inverse equations are proved on every cover and every bounded subset; the edge label j is retained. No path-count hypothesis is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-count"), DeclarationHandle.Create(Prefix + "actual_count"),
                H("Every actual labelled subset is counted once"), StatementSource.FromAuthor(Disp(All("n", Nat,
                    Eq(Call("actualCount", V("n")), Mul(Mul(D(2), V("n")), Call("restrictedCount", V("n"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Bool apex tag contributes two, the retained opposite rim label contributes n, and the inverse path correspondence contributes restrictedCount n. The source count is Nat.card of the type of actual vertex subsets satisfying closed domination, minimality among all proper dominating subsets, and induced connectivity. It is defined as zero for n<3, so the equality is for every natural n. Rotations and apex exchange are explicit bijections used for counting labels, not quotients."))), DescribeRole.Theorem)), []));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
