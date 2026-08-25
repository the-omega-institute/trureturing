using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class ResidualProgressMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Hilbert-space residual tails can retain full dimension while target-based "
            + "projection residuals decrease stage by stage.",
        H("Residual Progress Measures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-full-size-coordinate-tail-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/ResidualProgressMeasure."
                        + "bare_dimension_not_progress"),
                H("A strict residual chain can retain the ambient dimension"),
                StatementSource.FromAuthor(DimensionWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the real Hilbert space of square-summable natural-numbered "
                            + "sequences, let each stage be the closed coordinate tail.")),
                    Paragraph(Text(
                        "The zeroth tail is the whole space and every successor inclusion is "
                            + "strict. Reindexing the remaining Hilbert basis gives a linear "
                            + "isometry from every tail to the ambient space.")),
                    Paragraph(Text(
                        "The ambient carrier is also proved infinite-dimensional, so the "
                            + "unchanged Hilbert dimension cannot detect the strict descent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-and-test-residual-measures-descend"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/ResidualProgressMeasure."
                        + "target_residual_measures_antitone"),
                H("Target and test-family residual measures descend"),
                StatementSource.FromAuthor(TargetMeasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an antitone family of orthogonally complemented residual "
                            + "subspaces, projection through a later stage factors through "
                            + "projection at every earlier stage.")),
                    Paragraph(Text(
                        "Projection contraction therefore makes each fixed-vector norm "
                            + "antitone. Taking a complete-lattice supremum in the extended "
                            + "nonnegative reals preserves that order for every test family.")),
                    Paragraph(Text(
                        "The extended supremum also covers empty and unbounded test families. "
                            + "Kernel intersections are not included because no stagewise "
                            + "kernel order is specified by this norm-residual framework."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("antitone-residual-order-is-required"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/ResidualProgressMeasure."
                        + "antitone_residual_chain_is_necessary"),
                H("Residual order is required for descent"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the two-element stage order, take the residual to move from the "
                            + "zero subspace to the whole real line.")),
                    Paragraph(Text(
                        "This family is not antitone, and the projection norm of the target "
                            + "one increases from zero to one. Thus the residual-order "
                            + "hypothesis in the monotonicity theorem is necessary."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula DimensionWitnessFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("ell", D(2), naturals);
        Formula residual = F.Id("R");
        Formula n = F.Id("n");
        Formula next = Seq(n, Sp, Plus, Sp, D(1));

        return Disp(Seq(
            Exists, Sp, residual, Colon, Sp, naturals, Sp, To, Sp,
            Call("ClosedSubspace", space), Comma, Sp,
            Sub(residual, D(0)), Sp, Eq, Sp, space, Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            Call("StrictSubset", Sub(residual, next), Sub(residual, n)), Close,
            Sp, Land, Sp, Call("Antitone", residual), Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            Call("LinearIsometric", reals, Sub(residual, n), space), Close,
            Sp, Land, Sp, Call("InfiniteDimensional", reals, space), Dot));
    }

    private static Formula TargetMeasureFormula()
    {
        Formula residual = F.Id("R");
        Formula i = F.Id("i");
        Formula x = F.Id("x");
        Formula tests = F.Id("T");
        Formula projection = Seq(Call("P", Sub(residual, i)), Open, x, Close);
        Formula pointMeasure = new Formula.Norm(projection);
        Formula testMeasure = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(x, InMacro, Sp, tests), Sp, pointMeasure);

        return Disp(Seq(
            Call("Antitone", residual), Sp, Rightarrow, Sp,
            Open, Forall, Sp, x, Comma, Sp,
            Call("Antitone", Sub(pointMeasure, i)), Close, Sp, Land, RowBreak,
            Call("Antitone", Sub(testMeasure, i)), Dot));
    }

    private static Formula NecessityFormula()
    {
        Formula residual = F.Id("R");
        Formula pointMeasure = new Formula.Norm(
            Seq(Call("P", Sub(residual, F.Id("i"))), Open, D(1), Close));

        return Disp(Seq(
            Exists, Sp, residual, Colon, Sp, Call("Bool"), Sp, To, Sp,
            Call("ClosedSubspace", Seq(Mathbb, Grp(F.Id("R")))), Comma, Sp,
            Neg, Sp, Call("Antitone", residual), Sp, Land, Sp,
            Neg, Sp, Call("Antitone", Sub(pointMeasure, F.Id("i"))), Dot));
    }
}
