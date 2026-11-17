using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Hall;

internal sealed class PrescribedDifferencesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/hollmann2023simplex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hall's prescribed differences in a finite abelian group are realizable by two full numberings exactly when their sum is zero.",
        H("Hall's prescribed differences"), Blocks(
            Describe.Lean(
                DescribeId.Create("hall-prescribed-differences"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/Hall/PrescribedDifferences.numbering_iff_sum_eq_zero"),
                H("The zero-sum condition exactly characterizes realizability"),
                StatementSource.FromAuthor(Disp(ExactStatement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every universe u, let G be any finite additive abelian group and let n=Nat.card(G). A prescribed sequence r has domain Fin(n); these are occurrence indices, so equal or zero labels remain separate entries. Equiv(Fin(n),G) means a full input numbering. Shift(x,r) is the function i mapped to x(i)+r(i), and Sum(r) is the sum over every index in Fin(n). The formula asserts that a full input numbering with bijective Shift(x,r) exists if and only if Sum(r)=0. It includes the trivial group and has no parity, cyclicity, label-injectivity or supplied-service assumption.")),
                    Paragraph(Text("The construction follows the ordinary servicing argument of Hollmann, Khathuria, Riet and Skachek, Definition 4.1 and Theorems 4.2 and 4.4. For a partial service, both its input map x and its output map y=x+r are injective. Two unused outputs a,b define c=b-rzero+a. Extend the two injections x and c-y to a permutation q of G. Starting at t=c-b, follow q until the first point outside the old input range. Finiteness guarantees this exit: t has no predecessor in the old input range, while its inverse image under q lies in its finite orbit.")),
                    Paragraph(Text("Let S be the initial orbit segment before that exit. Replace x(i) by q(x(i)) exactly when x(i) lies in S. Forward closure within the old inputs prevents collisions between moved and unmoved inputs. The moved output equals c-x(i); backward closure prevents collisions between moved and unmoved outputs. The unused output a excludes the one extra output collision, and the unused output b excludes the one extra input collision. Adding the input t with the new label rzero therefore extends the service by one occurrence. This exchange is proved in the private service_extend lemma and consumed by induction in service_exists.")),
                    Paragraph(Text("Build the service for n-1 occurrences. The two injections omit one input a and one output b; Mathlib's unique missing-point theorem supplies them. Adjoining these points makes both maps bijective. Reindexing their sums and using the prescribed total zero forces a plus the remaining label to equal b. This proves sufficiency, including n=1 where the partial service is empty. Necessity reindexes the two full sums and cancels their common group total. The total of all elements of G is never assumed to be zero.")),
                    Paragraph(Text("This is Hall's known prescribed-difference theorem. The cited arXiv servicing proof is the proof source; the original Hall article was not read. The contribution is its kernel-checked construction in the pinned Lean libraries, with no novelty claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula ExactStatement()
    {
        var g = F.Id("G"); var r = F.Id("r"); var x = F.Id("x");
        var index = Call("Fin", Call("NatCard", g));
        var exists = Ex("x", Call("Equiv", index, g), Call("Bijective", Call("Shift", x, r)));
        var result = new Formula.Logic(exists, FormulaLogicOperator.Iff, Eq(Call("Sum", r), D(0)));
        return All("G", F.Id("Typeu"), Seq(
            OpenBracket, Call("AddCommGroup", g), CloseBracket, Sp,
            OpenBracket, Call("Finite", g), CloseBracket, Sp,
            All("r", new Formula.TypeArrow(index, g), result)));
    }
}
