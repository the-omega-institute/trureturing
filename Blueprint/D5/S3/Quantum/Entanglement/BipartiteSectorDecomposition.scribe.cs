using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class BipartiteSectorDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Traceless bipartite Hermitian tensors split into three orthogonal sectors.",
        H("Bipartite Hermitian Sector Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hermitian-space-has-square-real-dimension"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition."
                        + "hermitian_space_finrank"),
                H("Hermitian matrices have square real dimension"),
                StatementSource.FromAuthor(HermitianSpaceFinrankFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real vector space of Hermitian complex d-by-d matrices has "
                            + "dimension d squared. Thus imposing Hermitian symmetry halves "
                            + "the real dimension of the unrestricted complex matrix space.")),
                    Paragraph(Text(
                        "The dimension calculation decomposes every complex matrix uniquely "
                            + "into its Hermitian real part and i times its Hermitian imaginary "
                            + "part. Comparing the two resulting copies and cancelling their "
                            + "common factor gives the stated square dimension."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-zero-hermitian-space-has-codimension-one"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition."
                        + "trace_zero_hermitian_finrank"),
                H("Traceless Hermitian matrices have codimension one"),
                StatementSource.FromAuthor(TraceZeroHermitianFinrankFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive d, the traceless Hermitian matrices form a real subspace "
                            + "of dimension d squared minus one. The missing direction is exactly "
                            + "the scalar identity line.")),
                    Paragraph(Text(
                        "The Hilbert--Schmidt inner product with the identity reads off the real "
                            + "trace of a Hermitian matrix. Consequently the trace-zero space is "
                            + "the orthogonal complement of the nonzero identity line, so its "
                            + "dimension is one less than that of the full Hermitian space."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "bipartite-traceless-hermitian-space-splits-into-three-sectors"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition."
                        + "bipartite_sector_decomposition"),
                H("The bipartite traceless space splits into three orthogonal sectors"),
                StatementSource.FromAuthor(BipartiteSectorDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two nonzero finite dimensions, the traceless bipartite Hermitian "
                            + "space consists of three sectors: a traceless operator on A tensored "
                            + "with the scalar identity on B, the symmetric local sector on B, "
                            + "and operators traceless in both factors.")),
                    Paragraph(Text(
                        "The three sectors are pairwise orthogonal for the real "
                            + "Hilbert--Schmidt inner product, and their join is the entire "
                            + "orthogonal complement of the scalar-scalar identity line. This "
                            + "gives an orthogonal internal decomposition rather than only a "
                            + "dimension count.")),
                    Paragraph(Text(
                        "Their real dimensions are respectively m squared minus one, n squared "
                            + "minus one, and the product of those two quantities. Tensor-product "
                            + "inner products establish orthogonality, while the product dimension "
                            + "formula and the codimension-one identity sector show that the "
                            + "contained sum already has the full traceless dimension."))),
                DescribeRole.Theorem))));

    private static Formula HermitianSpaceFinrankFormula()
    {
        Formula dimension = F.Id("d");

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            Call("finrankR", Call("HermitianSpace", dimension)), Sp, Eq, Sp,
            dimension, Caret, Grp(D(2)), Dot));
    }

    private static Formula TraceZeroHermitianFinrankFormula()
    {
        Formula dimension = F.Id("d");

        return Disp(Seq(
            Forall, Sp, dimension, Sp, Geq, Sp, D(1), Comma, Sp,
            Call("finrankR", Call("traceZeroHermitian", dimension)), Sp, Eq, Sp,
            SquareMinusOne(dimension), Dot));
    }

    private static Formula BipartiteSectorDecompositionFormula()
    {
        Formula firstDimension = F.Id("m");
        Formula secondDimension = F.Id("n");
        Formula localA = Call("localASector", firstDimension, secondDimension);
        Formula localB = Call("localBSector", firstDimension, secondDimension);
        Formula correlation = Call("correlationSector", firstDimension, secondDimension);
        Formula traceZero = Call("bipartiteTraceZero", firstDimension, secondDimension);
        Formula firstRank = SquareMinusOne(firstDimension);
        Formula secondRank = SquareMinusOne(secondDimension);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, firstDimension, Comma, Sp, secondDimension, Comma, Sp,
            firstDimension, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            secondDimension, Sp, Geq, Sp, D(1), Sp, Rightarrow, Sp, RowBreak, Grp(),
            Call("Sup", localA, localB, correlation), Sp, Eq, Sp, traceZero,
            Sp, Land, RowBreak, Grp(),
            Call("Orthogonal", localA, localB), Sp, Land, Sp,
            Call("Orthogonal", localA, correlation), Sp, Land, RowBreak, Grp(),
            Call("Orthogonal", localB, correlation), Sp, Land, RowBreak, Grp(),
            Call("finrankR", localA), Sp, Eq, Sp, firstRank,
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", localB), Sp, Eq, Sp, secondRank,
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", correlation), Sp, Eq, Sp,
            firstRank, Sp, Times, Sp, secondRank, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula SquareMinusOne(Formula value) =>
        Seq(value, Caret, Grp(D(2)), Sp, Minus, Sp, D(1));
}
