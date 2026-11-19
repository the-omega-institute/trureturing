using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class TalagrandFiniteFibresDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-to-one maps on the Talagrand compactum have finitely many multiple fibres.",
        H("Finite fibres on the Talagrand compactum"), Blocks(
            Describe.Lean(DescribeId.Create("grothendieck"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.Grothendieck"),
                H("The Grothendieck property of the real continuous dual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the dual of the real continuous functions on K, convergence of a sequence on every continuous function to the evaluations of a fixed functional implies convergence to that functional on every continuous linear bidual test."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-subseq-pairwise-clopen-separation"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_subseq_pairwise_clopen_separation"),
                H("Simultaneous clopen separation along a subsequence"),
                StatementSource.FromAuthor(Disp(All("K", V("ZeroDimensionalCompactHausdorffSpaces"),
                    Imp(Call("Grothendieck", V("K")),
                        All("I", V("NonemptyCountableTypes"),
                            All("x", Call("Arrays", V("I"), V("K")),
                                Imp(And(Call("DisjointColumns", V("x")), Call("EventuallyDistinctRows", V("x"))),
                                    Call("EventuallyClopenSeparatedSubsequence", V("x"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let K be compact Hausdorff and zero-dimensional with the Grothendieck property, and let I be nonempty and countable. Columns of x are indexed by the natural numbers and have disjoint sets of values. Distinct rows differ eventually. There is a single strictly increasing subsequence such that for every ordered pair of distinct rows, one clopen eventually contains the first row and excludes the second.")),
                    Paragraph(Text(
                    "Finite clopen tests separate the Dirac differences of disjoint pairs. Weak-star compactness gives a single bidual test taking value one on every difference. If each clopen separated the ordered pairs only finitely often, compactness of the space of pairs would force the differences to converge to zero on every continuous function, contradicting the Grothendieck property. Successive extraction and diagonalization handle all ordered pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-uniform-fibre-bound"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_uniform_fibre_bound"),
                H("A uniform bound on finite fibres"),
                StatementSource.FromAuthor(Disp(All("K", V("ZeroDimensionalCompactHausdorffSpaces"),
                    Imp(Call("Grothendieck", V("K")), All("Y", V("HausdorffSpaces"),
                        All("q", Call("ContinuousMaps", V("K"), V("Y")),
                            Imp(Call("AllFibresFinite", V("q")), Call("UniformFibreBound", V("q"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let K be compact Hausdorff and zero-dimensional with the Grothendieck property, and let Y be Hausdorff. If each fibre of q is finite, their cardinalities share a natural-number bound. Otherwise enumerate larger and larger fibres over distinct points and separate their countably many rows. A cluster tuple has pairwise distinct coordinates with the same image under q."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-finite-to-one"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.actual_finite_to_one"),
                H("Finitely many nonsingleton fibres on the CH Talagrand compactum"),
                StatementSource.FromAuthor(Disp(All("hCH", V("ContinuumEqualsAlephOne"),
                    All("Y", V("HausdorffSpaces"),
                        All("q", Call("ContinuousMaps", Call("ActualFinalLimit", V("hCH")), V("Y")),
                            Imp(Call("AllFibresFinite", V("q")),
                                And(Call("UniformFibreBound", V("q")),
                                    Call("FinitelyManyNonsingletonFibres", V("q"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(Paragraph(Text(
                    "The domain is SignedOrdinalRealization.finalPrefix(hCH).LimitSpace and Y is Hausdorff. Every continuous map with finite fibres admits a uniform cardinal bound, and only finitely many fibres contain at least two points.")),
                    Paragraph(Text(
                    "If infinitely many fibres were nonsingleton, choose the largest size occurring infinitely often and place the points of those fibres in disjoint clopens. A convergent sequence of distinct image points would lift to a sequence whose cluster set is finite. A closed neighborhood isolating one cluster point would give a convergent subsequence of distinct points in K. Thus the separated fibres accumulate away from the finitely many larger fibres. An infinite closed set of such image points lifts homeomorphically into each clopen, contradicting the finite-image endpoint for disjoint copies."))),
                DescribeRole.Theorem))));
}
