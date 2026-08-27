using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class RobustFrameBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted finite readouts have sharp spectral frame bounds.",
        H("Robust Frame Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robust-observer-frame-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/RobustFrameBounds."
                        + "robust_observer_frame_bounds"),
                H("Weighted readouts have sharp frame bounds"),
                StatementSource.FromAuthor(FrameBoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d exceed one and let a finite index type label nonnegative "
                            + "weights and Hermitian effects. The analysis map sends a real "
                            + "trace-zero Hermitian perturbation to its weighted "
                            + "Hilbert--Schmidt effect coordinates.")),
                    Paragraph(Text(
                        "The lower and upper constants are the least and greatest eigenvalues "
                            + "of the adjoint Gram operator. Expanding in its ordered "
                            + "orthonormal eigenbasis gives both quadratic frame bounds.")),
                    Paragraph(Text(
                        "The least endpoint is positive exactly when the analysis map is "
                            + "injective. Squared singular values are the Gram eigenvalues, "
                            + "so the singular-value condition ratio is the square root of "
                            + "the endpoint ratio.")),
                    Paragraph(Text(
                        "The dimension premise excludes d equal to one, whose trace-zero "
                            + "Hermitian carrier has dimension zero and therefore has no least "
                            + "Gram eigenvalue in the source construction."))),
                DescribeRole.Theorem))));

    private static Formula FrameBoundsFormula()
    {
        Formula d = F.Id("d");
        Formula indexType = F.Id("I");
        Formula index = F.Id("i");
        Formula weights = F.Id("w");
        Formula effects = F.Id("E");
        Formula vector = F.Id("D");
        Formula analysis = F.Id("A");
        Formula alpha = Alpha;
        Formula beta = Beta;
        Formula condition = Kappa;
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula traceZero = Call("traceZeroHermitian", d);
        Formula hermitian = Call("HermitianSpace", d);
        Formula euclidean = Call("EuclideanSpace", real, indexType);
        Formula analysisType = Call("LinearMap", real, traceZero, euclidean);
        Formula coordinate = new Formula.Subscript(Call(analysis, vector), Seq(index));
        Formula weightedCoordinate = Seq(
            Sqrt, Grp(new Formula.Subscript(weights, index)), Sp,
            Langle, Sp, vector, Comma, Sp,
            new Formula.Subscript(effects, index), Rangle, Underscore, Grp(real));
        Formula gram = Seq(analysis, Caret, Grp(Star), Sp, analysis);
        Formula normVectorSq = Seq(new Formula.Norm(vector), Caret, Grp(D(2)));
        Formula normAnalysisSq = Seq(
            new Formula.Norm(Call(analysis, vector)), Caret, Grp(D(2)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp,
            Call("NeZero", d), Comma, Sp,
            indexType, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Fintype", indexType), Comma, RowBreak, Grp(),
            weights, Colon, Sp, indexType, Sp, To, Sp, F.Id("NNReal"), Comma, Sp,
            effects, Colon, Sp, indexType, Sp, To, Sp, hermitian, Comma,
            RowBreak, Grp(),
            D(1), Sp, Lt, Sp, d, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            analysis, Colon, Sp, analysisType, Comma, Sp,
            coordinate, Sp, Colon, Eq, Sp, weightedCoordinate, Comma,
            RowBreak, Grp(),
            alpha, Sp, Colon, Eq, Sp, Call("lambdaMin", gram), Comma, Sp,
            beta, Sp, Colon, Eq, Sp, Call("lambdaMax", gram), Comma,
            RowBreak, Grp(),
            condition, Sp, Colon, Eq, Sp,
            Frac, Grp(Call("sigmaMax", analysis)),
                Grp(Call("sigmaMin", analysis)), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, vector, Colon, Sp, traceZero, Comma, Sp,
            alpha, Sp, normVectorSq, Sp, Leq, Sp, normAnalysisSq, Sp,
            Land, Sp, normAnalysisSq, Sp, Leq, Sp, beta, Sp, normVectorSq,
            Close, Sp, Land,
            RowBreak, Grp(),
            Open, Call("Injective", analysis), Sp, Iff, Sp,
            D(0), Sp, Lt, Sp, alpha, Close, Sp, Land,
            RowBreak, Grp(),
            condition, Sp, Eq, Sp, Sqrt, Grp(Frac, Grp(beta), Grp(alpha)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
