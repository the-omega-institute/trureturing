using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class ObservableKrylovGrowthBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict growth of the finite observable Krylov tower is bounded by missing rank.",
        H("Observable Krylov Growth Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observable-krylov-strict-growth-bound"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound."
                        + "observable_krylov_strict_growth_bound"),
                H("Strict observable-tower growth is rank bounded"),
                StatementSource.FromAuthor(GrowthBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field, let T evolve V linearly, and let C read V "
                            + "linearly into Y. The m-th observable Krylov space is constructed "
                            + "as the span of (T*)^k(C*y) for k at most m.")),
                    Paragraph(Text(
                        "The set of indices where this canonical tower grows strictly has "
                            + "cardinality at most dim(V) minus rank(C). This is the theorem's "
                            + "sole public clause; the dimension increase and initial-rank "
                            + "identity are its proof, not independent conjuncts.")),
                    Paragraph(Text(
                        "Every strict inclusion raises finrank, so sending a growth index to "
                            + "the current finrank injects it into the natural interval from "
                            + "rank(C) to dim(V). The zero-stage space is range(C*), whose "
                            + "finrank equals rank(C).")),
                    Paragraph(Text(
                        "Required-family and pinned-Mathlib searches found no packaged Krylov "
                            + "growth-count theorem. The proof directly applies Mathlib's "
                            + "strict-submodule finrank inequality, adjoint-range rank identity, "
                            + "injective set-cardinality bound, and natural-interval count."))),
                DescribeRole.Theorem))));

    private static Formula GrowthBoundFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula depth = F.Id("m");
        Formula current = Call("observableKrylov", evolution, readout, depth);
        Formula next = Call("observableKrylov", evolution, readout, Add(depth, Num(1)));
        Formula strictGrowth = new Formula.Relation(
            current,
            FormulaRelationOperator.LessThan,
            next);
        Formula strictIndices = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, F.Id("N"), Sp,
            Mid, Sp, strictGrowth, CloseBrace);
        Formula rankGap = Subtract(
            Call("finrank", scalar, state),
            Call("finrank", scalar, Call("range", readout)));
        Formula bound = new Formula.Relation(
            Call("encard", strictIndices),
            FormulaRelationOperator.LessThanOrEqual,
            rankGap);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Comma, Sp, evolution, Comma, Sp, readout, Comma, Esc,
            bound, Dot));
    }
}
