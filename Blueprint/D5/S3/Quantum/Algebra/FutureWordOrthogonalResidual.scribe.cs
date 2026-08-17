using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FutureWordOrthogonalResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite expectation words characterize residuals and visible projections.",
        H("Future Words and Orthogonal Residuals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-word-equality-is-orthogonal-residual-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/FutureWordOrthogonalResidual."
                    + "future_word_orthogonal_residual"),
                H("Finite-word equality is orthogonal-residual equivalence"),
                StatementSource.FromAuthor(FutureWordResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of effects generate the visible subspace. The "
                            + "expectation word of a represented state records its inner product "
                            + "with each effect. Equality of two such words is equivalent to the "
                            + "difference of the represented states lying in the orthogonal "
                            + "complement of the visible span.")),
                    Paragraph(Text(
                        "The same residual condition is equivalent to equality of the two "
                            + "canonical orthogonal projections onto the visible span. Both "
                            + "equivalences appear as explicit conjuncts in the named theorem.")),
                    Paragraph(Text(
                        "Repository search found the existing complementary-projection machinery "
                            + "but no theorem with this complete finite-word characterization. "
                            + "Loogle returned exact single hits for the span-induction, "
                            + "orthogonality, and zero-projection declarations applied by the "
                            + "proof. The attempted shaped LeanSearch API query returned HTTP "
                            + "404."))),
                DescribeRole.Theorem))));

    private static Formula FutureWordResidualFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula state = F.Id("S");
        Formula depth = F.Id("m");
        Formula effect = F.Id("e");
        Formula embedding = F.Id("X");
        Formula visible = Seq(
            Operatorname, Grp(F.Id("span")), Underscore, Grp(scalar), Open,
            Operatorname, Grp(F.Id("range")), Open, effect, Close, Close);
        Formula residual = Seq(visible, Caret, Grp(Perp));
        Formula xRho = Seq(embedding, Open, Rho, Close);
        Formula xSigma = Seq(embedding, Open, SigmaLower, Close);
        Formula difference = Seq(xRho, Sp, Minus, Sp, xSigma);
        Formula wordRho = Seq(
            F.Id("W"), Underscore, Grp(depth), Caret, Grp(effect, Comma, embedding),
            Open, Rho, Close);
        Formula wordSigma = Seq(
            F.Id("W"), Underscore, Grp(depth), Caret, Grp(effect, Comma, embedding),
            Open, SigmaLower, Close);
        Formula projectionRho = Seq(
            F.Id("P"), Underscore, Grp(visible), Open, xRho, Close);
        Formula projectionSigma = Seq(
            F.Id("P"), Underscore, Grp(visible), Open, xSigma, Close);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, state, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("InnerProductSpace")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("FiniteDimensional")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            depth, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            effect, Colon, Sp, Operatorname, Grp(F.Id("Fin")),
            Open, depth, Sp, Plus, Sp, D(1), Close, Sp, To, Sp, space, Comma, Esc,
            embedding, Colon, Sp, state, Sp, To, Sp, space, Comma, Esc,
            Rho, Comma, Sp, SigmaLower, Sp, InMacro, Sp, state, Comma, Esc,
            Open,
            Open, wordRho, Sp, Eq, Sp, wordSigma, Close,
            Sp, Leftrightarrow, Sp,
            Open, difference, Sp, InMacro, Sp, residual, Close,
            Close,
            Sp, Land, Sp,
            Open,
            Open, difference, Sp, InMacro, Sp, residual, Close,
            Sp, Leftrightarrow, Sp,
            Open, projectionRho, Sp, Eq, Sp, projectionSigma, Close,
            Close, Dot));
    }
}
