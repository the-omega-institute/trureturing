using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.CountableSlices;

internal sealed class CountableFiniteSliceResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countably many finite Hilbert slices generate only a separable cumulative space.",
        H("Countable Finite-Slice Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countable-finite-slice-separable-and-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/CountableSlices/CountableFiniteSliceResidual."
                        + "countable_finite_slice_separable_and_residual"),
                H("Finite countable slicing leaves a residual in nonseparable space"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a complete real or complex Hilbert space. Starting from a "
                            + "finite-dimensional subspace S0, stage n is constructed from S0 "
                            + "and the first n finite-dimensional slices. Each next slice is "
                            + "required to lie in the orthogonal residual of the prior stage.")),
                    Paragraph(Text(
                        "A finite basis makes every stage a separable subset. The countable union "
                            + "of the stages remains separable, as do its linear span and closure. "
                            + "This closure is the completion family's canonical cumulativeSpace.")),
                    Paragraph(Text(
                        "The canonical residualSpace is the cumulative orthogonal complement. If "
                            + "that residual were zero, Mathlib's orthogonal_eq_bot_iff would make "
                            + "the cumulative space all of H, contradicting nonseparability.")),
                    Paragraph(Text(
                        "The completion family's existing cumulativeSpace and residualSpace are "
                            + "imported as the single source of truth. Pinned Mathlib has no exact "
                            + "combined theorem; the proof applies its countable-union, span, "
                            + "closure, subtype-separability, and orthogonal-complement results.")),
                    Paragraph(Text(
                        "The full one-dimensional initial stage and zero slice family over the "
                            + "real line compiles as a "
                            + "simultaneous witness for the carrier, recursion premise, and both "
                            + "public conclusions."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction"))]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula initial = new Formula.Subscript(F.Id("S"), D(0));
        Formula slice = F.Id("E");
        Formula n = F.Id("n");
        Formula nextSlice = new Formula.Subscript(slice, Seq(n, Plus, D(1)));
        Formula stage = new Formula.Subscript(F.Id("S"), n);
        Formula cumulative = new Formula.Subscript(F.Id("S"), Infty);
        Formula residual = new Formula.Subscript(F.Id("R"), Infty);
        Formula priorSum = Seq(
            initial, Sp, Operatorname, Grp(F.Id("orthogonalSum")), Sp,
            Call("finiteSliceSum", slice, n));
        Formula stageConstruction = Seq(stage, Sp, Eq, Sp, priorSum);
        Formula sliceCondition = Seq(
            nextSlice, Sp, Subseteq, Sp,
            Call("OrthogonalComplement", stage));
        Formula cumulativeConstruction = Seq(
            cumulative, Sp, Eq, Sp,
            Call("ClosureUnion", F.Id("S")));
        Formula residualConstruction = Seq(
            residual, Sp, Eq, Sp,
            Call("OrthogonalComplement", cumulative));
        Formula zeroSubspace = Seq(OpenBrace, D(0), CloseBrace);

        return Disp(Seq(
            Forall, Sp, scalar, Colon, Sp, Call("RCLikeField"), Comma, Esc,
            Forall, Sp, space, Colon, Sp, Call("CompleteHilbertSpace", scalar), Comma, Esc,
            Forall, Sp, initial, Comma, Sp, slice, Comma, Esc,
            Call("FiniteDimensional", initial), Sp, Land, Sp,
            Open, Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("FiniteDimensional", nextSlice), Close, Sp, Land, Sp,
            Open, Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            stageConstruction, Sp, Land, Sp, sliceCondition, Close,
            Sp, Rightarrow, Sp,
            cumulativeConstruction, Sp, Land, Sp,
            residualConstruction, Sp, Land, Sp,
            Call("SeparableSpace", cumulative), Sp, Land, Sp,
            Open, Neg, Call("SeparableSpace", space), Sp, Rightarrow, Sp,
            residual, Sp, Neq, Sp, zeroSubspace, Close, Dot));
    }
}
