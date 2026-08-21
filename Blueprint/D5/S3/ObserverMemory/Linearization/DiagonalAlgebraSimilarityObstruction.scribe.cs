using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Linearization;

internal sealed class DiagonalAlgebraSimilarityObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Similar transition matrices need not admit a diagonal-algebra-preserving similarity.",
        H("Diagonal-Algebra Similarity Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("similar-transition-matrices-can-differ-as-based-systems"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Linearization/DiagonalAlgebraSimilarityObstruction."
                        + "same_linear_class_without_diagonal_algebra_similarity"),
                H("Similar transition matrices can differ as based systems"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The maps tauA and tauB are imported from the canonical eight-state "
                            + "countermodel. Their complex transition matrices use the standard "
                            + "basis: column y is the coordinate vector indexed by tau(y).")),
                    Paragraph(Text(
                        "The first public conjunct gives an explicit complex change of basis and "
                            + "two-sided inverse intertwining the transition matrices. This is the "
                            + "source's common complex linear similarity class, and hence its common "
                            + "Jordan form.")),
                    Paragraph(Text(
                        "The second public conjunct rules out any such change of basis that also "
                            + "conjugates every standard diagonal matrix to a diagonal matrix in "
                            + "both directions. Thus the quantified property is directly about the "
                            + "full diagonal algebra, not a definition by graph conjugacy.")),
                    Paragraph(Text(
                        "The proof applies the frozen integral similarity certificate after entrywise "
                            + "complex casting. Conversely, conjugated coordinate diagonals force each "
                            + "matrix column onto a distinct coordinate row, producing a permutation "
                            + "conjugacy forbidden by the frozen function-graph countermodel."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ObstructionFormula()
    {
        Formula stateType = Call("Fin", D(8));
        Formula scalarType = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrixType = Call("Matrix", stateType, stateType, scalarType);
        Formula functionType = new Formula.TypeArrow(stateType, scalarType);
        Formula first = Call("complexTransitionMatrix", F.Id("tauA"));
        Formula second = Call("complexTransitionMatrix", F.Id("tauB"));
        Formula change = F.Id("P");
        Formula inverse = F.Id("Q");
        Formula diagonal = F.Id("d");
        Formula transported = Seq(F.Id("d"), Apos);
        Formula identity = F.Id("I");

        Formula ordinarySimilarity = Seq(
            Open, Exists, Sp,
            Typed(Seq(change, Comma, Sp, inverse), matrixType), Comma, RowBreak, Grp(),
            change, inverse, Sp, Eq, Sp, identity, Sp, Land, Sp,
            inverse, change, Sp, Eq, Sp, identity, Sp, Land, RowBreak, Grp(),
            first, change, Sp, Eq, Sp, change, second, Close);

        Formula diagonalForward = Seq(
            Open, Forall, Sp, Typed(diagonal, functionType), Comma, Sp,
            Exists, Sp, Typed(transported, functionType), Comma, Sp,
            change, Call("diag", diagonal), inverse, Sp, Eq, Sp,
            Call("diag", transported), Close);

        Formula diagonalBackward = Seq(
            Open, Forall, Sp, Typed(diagonal, functionType), Comma, Sp,
            Exists, Sp, Typed(transported, functionType), Comma, Sp,
            inverse, Call("diag", diagonal), change, Sp, Eq, Sp,
            Call("diag", transported), Close);

        Formula preservingSimilarity = Seq(
            Open, Exists, Sp,
            Typed(Seq(change, Comma, Sp, inverse), matrixType), Comma, RowBreak, Grp(),
            change, inverse, Sp, Eq, Sp, identity, Sp, Land, Sp,
            inverse, change, Sp, Eq, Sp, identity, Sp, Land, RowBreak, Grp(),
            first, change, Sp, Eq, Sp, change, second, Sp, Land, RowBreak, Grp(),
            diagonalForward, Sp, Land, RowBreak, Grp(), diagonalBackward, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            ordinarySimilarity, Sp, Land, RowBreak, Grp(),
            Neg, preservingSimilarity, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
