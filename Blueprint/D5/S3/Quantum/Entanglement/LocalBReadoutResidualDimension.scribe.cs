using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class LocalBReadoutResidualDimensionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula localA = Call("localASector", m, n);
        Formula localB = Call("localBSector", m, n);
        Formula correlation = Call("correlationSector", m, n);
        Formula traceZero = Call("bipartiteTraceZero", m, n);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(m, nat), Comma, Sp, Typed(n, nat), Comma, Sp,
            m, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            n, Sp, Geq, Sp, D(1), Sp, Rightarrow, RowBreak, Grp(),
            Call("finrankR", traceZero), Sp, Eq, Sp,
            SquareMinusOne(Grp(Seq(m, Sp, Times, Sp, n))), Sp, Land, RowBreak, Grp(),
            Call("finrankR", localB), Sp, Eq, Sp,
            SquareMinusOne(n), Sp, Land, RowBreak, Grp(),
            Call("finrankR", Call("Sup", localA, correlation)), Sp, Eq, Sp,
            Seq(n, Caret, Grp(D(2))), Sp, Times, Sp, Grp(SquareMinusOne(m)), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Local B readout leaves the A-local and correlation sectors invisible.",
            H("Local B Readout Residual Dimension"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("local-b-readout-has-the-stated-invisible-dimension"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Entanglement/LocalBReadoutResidualDimension."
                            + "local_b_readout_residual_dimension"),
                    H("The B-local invisible sector has the stated dimension"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The canonical bipartite traceless Hermitian carrier splits into "
                                + "the A-local, B-local, and correlation sectors.")),
                        Paragraph(Text(
                            "A complete readout restricted to subsystem B occupies the B-local "
                                + "sector. Its invisible complement is the orthogonal join of the "
                                + "A-local and correlation sectors.")),
                        Paragraph(Text(
                            "The imported sector decomposition supplies orthogonality and the "
                                + "individual ranks; finite-dimensional join formulas give all "
                                + "three displayed dimensions."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula SquareMinusOne(Formula value) =>
        Seq(value, Caret, Grp(D(2)), Sp, Minus, Sp, D(1));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
