using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class LimitResidualDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The intersection of stage residuals is the cumulative orthogonal complement.",
        H("Limit Residual Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("limit-residual-is-the-cumulative-orthogonal-complement"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/LimitResidualDecomposition."
                        + "limit_residual_orthogonal_decomposition"),
                H("The limit residual is the cumulative orthogonal complement"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a sequence of subspaces in a complete real-or-complex "
                            + "inner-product space. Its cumulative space is the closure of the "
                            + "supremum of the stages.")),
                    Paragraph(Text(
                        "The limiting residual is constructed independently as the intersection "
                            + "of the orthogonal complements of all stages. It equals the "
                            + "orthogonal complement of the cumulative space.")),
                    Paragraph(Text(
                        "The equality identifies the two canonical constructions, and the second "
                            + "conjunct states that the cumulative space and limiting residual "
                            + "form an internal direct sum of the ambient Hilbert space."))),
                DescribeRole.Theorem))));

    private static Formula DecompositionFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula stages = F.Id("S");
        Formula visible = Call("cumulativeSpace", stages);
        Formula residual = Call("limitingResidual", stages);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp,
            Call("CompleteHilbertSpace", scalar, space), Comma,
            RowBreak, Grp(),
            stages, Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
            Call("Subspace", scalar, space), Comma,
            RowBreak, Grp(),
            residual, Sp, Eq, Sp, visible, Caret, Grp(Perp), Sp, Land,
            RowBreak, Grp(),
            Call("IsCompl", visible, residual), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
