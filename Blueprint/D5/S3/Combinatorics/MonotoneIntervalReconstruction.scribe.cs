using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class MonotoneIntervalReconstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hegyvari2026consecutivesums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unlabelled interval sums determine every nonnegative nondecreasing real list of length at least three.",
        H("Reconstruction from full interval sums"),
        Blocks(Describe.Lean(DescribeId.Create("monotone-interval-reconstruction"),
            DeclarationHandle.Create("D5/S3/Combinatorics/MonotoneIntervalReconstruction.result"),
            H("Zeros, equal entries and coincident observations"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("A and B are arbitrary finite lists of exact real numbers. "
                    + "Nonnegative(L) means that every entry x of L satisfies 0≤x. "
                    + "Nondecreasing(L) means L.Pairwise (·≤·) in the original index order. "
                    + "Equal adjacent entries and zeros are allowed. C(L) is the multiset "
                    + "containing one occurrence of the inclusive sum from i through j for "
                    + "every 0≤i<j<length(L). All multiplicities are retained. The input "
                    + "provides neither interval labels nor singleton sums. The two lengths "
                    + "are not assumed equal.")),
                Paragraph(Text("The mathematical source is Omega.MonotoneIntervalReconstruction.list_reconstruct "
                    + "in OmegaMath.Combinatorics.MonotoneIntervalReconstruction. The D5 result "
                    + "is its book citation. The source defines intervals n as the filtered "
                    + "Cartesian product of range n with itself and maps each endpoint pair "
                    + "to the sum over Finset.Icc. Thus each interval contributes once, even "
                    + "when many pairs have the same value. The list accessor getD is used "
                    + "only at indices inside the list; its default does not affect C.")),
                Paragraph(Text("Cardinality of C first determines the positive length: increasing "
                    + "n strictly enlarges the interval set. The maximum observation is the "
                    + "whole-list sum T. After removing exactly the single occurrence indexed "
                    + "by the whole list, the maximum is the sum S from index 1 to n−1. "
                    + "Every other proper interval omits either the first or the last entry; "
                    + "nonnegativity and nondecreasing order bound its sum by S. Hence the "
                    + "first entry is T−S. This argument also applies when T=S and the "
                    + "largest observed value has several occurrences.")),
                Paragraph(Text("For a known prefix of k entries, partition the actual endpoint "
                    + "pairs into j<k and j≥k. Their mapped multisets add to the full data. "
                    + "Equal prefixes give exactly equal first parts, which cancel with "
                    + "multiplicity. In the remaining multiset the boundary interval "
                    + "(k−1,k) occurs, and every remaining interval has value at least "
                    + "a(k−1)+a(k): its last two entries dominate that pair and all further "
                    + "entries are nonnegative. This is a statement about the minimum value; "
                    + "no unique occurrence is asserted. Equal residual data and the equal "
                    + "previous entry force equal next entries. Starting at k=1 recovers "
                    + "the second entry as well, and induction synchronizes the whole list.")),
                Paragraph(Text("Hegyvári, Pach and Tang, Consecutive sums and Reconstructing Problems, "
                    + "arXiv:2611.30462v1, Section 4.1, Proposition 4.1, supply the extremal "
                    + "initialization and residual-minimum proof route for positive strictly "
                    + "increasing integer lists. The real, zero and weak-order extension "
                    + "here is derived in this repository. The source and scope are recorded "
                    + "in Library/Combinatorics/hegyvari2026consecutivesums.md. This theorem "
                    + "claims mathematical uniqueness only; it makes no arithmetic-operation, "
                    + "bit-complexity or RAM bound and does not solve general Turnpike. "
                    + "The bounded source and Lean search does not establish worldwide novelty."))),
            DescribeRole.Theorem))));

    private static Formula V(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Statement()
    {
        var A = V("A"); var B = V("B");
        var realList = Call("List", V("Real"));
        return All("A", realList, All("B", realList,
            Imp(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, Call("length", A)),
            Imp(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, Call("length", B)),
            Imp(Call("Nonnegative", A), Imp(Call("Nonnegative", B),
            Imp(Call("Nondecreasing", A), Imp(Call("Nondecreasing", B),
            Imp(Rel(Call("C", A), FormulaRelationOperator.Equal, Call("C", B)),
                Rel(A, FormulaRelationOperator.Equal, B))))))))));
    }
}
