using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FiniteLayerProjectionEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero orthogonal residual contains a unit vector at distance one.",
        H("Finite-Layer Projection Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-nonzero-orthogonal-residual-has-a-unit-escape-vector"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/FiniteLayerProjectionEscape."
                    + "finite_layer_projection_escape"),
                H("A nonzero orthogonal residual has a unit escape vector"),
                StatementSource.FromAuthor(ProjectionEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a closed subspace of a complete real or complex inner-product "
                            + "space. If its orthogonal complement is nonzero, there is a unit "
                            + "vector e in that complement. The projection onto S annihilates e, "
                            + "and the distance from e to S is exactly one.")),
                    Paragraph(Text(
                        "The same hypothesis makes the projection onto the orthogonal complement "
                            + "nonzero. That projection equals the identity minus the projection "
                            + "onto S and has operator norm one.")),
                    Paragraph(Text(
                        "The proof reuses the repository's complementary-projection identity. "
                            + "Pinned Mathlib supplies the nonzero subspace witness, the minimal-"
                            + "distance characterization of orthogonal projection, and the exact "
                            + "norm of a nonzero orthogonal projection. Natural-language name "
                            + "searches found no single declaration bundling all conclusions."))),
                DescribeRole.Theorem))));

    private static Formula ProjectionEscapeFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("V");
        Formula subspace = F.Id("S");
        Formula vector = F.Id("e");
        Formula complement = Seq(subspace, Caret, Grp(Perp));
        Formula projection = Seq(F.Id("P"), Underscore, Grp(subspace));
        Formula identity = F.Id("I");

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Underscore,
            Grp(scalar), Open, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, space, Close,
            CloseBracket, Comma, Esc,
            subspace, Colon, Sp, Operatorname, Grp(F.Id("ClosedSubmodule")), Underscore,
            Grp(scalar), Open, space, Close, Comma, Esc,
            complement, Sp, Neq, Sp, OpenBrace, D(0), CloseBrace,
            Sp, Rightarrow, Sp,
            Exists, Sp, vector, Colon, Sp, space, Comma, Esc,
            vector, Sp, InMacro, Sp, complement, Sp, Land, Sp,
            Call("norm", vector), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            projection, Open, vector, Close, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Operatorname, Grp(F.Id("infDist")), Open, vector, Comma, subspace, Close,
            Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("norm", Seq(identity, Sp, Minus, Sp, projection)), Sp, Eq, Sp, D(1), Dot));
    }
}
