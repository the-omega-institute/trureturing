using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OrthogonalProjectionComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementary orthogonal projections satisfy the six canonical operator identities.",
        H("Orthogonal Projections onto Complementary Subspaces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-subspace-projections-obey-the-complement-identities"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrthogonalProjectionComplement."
                    + "orthogonal_complement_projection_identities"),
                H("Closed-subspace projections obey the complement identities"),
                StatementSource.FromAuthor(ProjectionIdentitiesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a closed subspace of a complete real or complex inner-product "
                            + "space, and let P with subscript M denote its orthogonal projection. "
                            + "The projection onto the orthogonal complement is the identity minus "
                            + "P with subscript M.")),
                    Paragraph(Text(
                        "Both projections are idempotent. Their compositions vanish in both "
                            + "orders, and their sum is the identity operator. These are all six "
                            + "equalities in the named statement, retained as one conjunction.")),
                    Paragraph(Text(
                        "Loogle and the pinned Mathlib tree supplied the exact complementary, "
                            + "idempotence, orthogonality, and sum declarations used by the Lean "
                            + "proof. The LeanSearch endpoint attempted for corroboration returned "
                            + "HTTP 404."))),
                DescribeRole.Theorem))));

    private static Formula ProjectionIdentitiesFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula subspace = F.Id("M");
        Formula complement = Seq(subspace, Caret, Grp(Perp));
        Formula projection = Seq(F.Id("P"), Underscore, Grp(subspace));
        Formula complementProjection = Seq(F.Id("P"), Underscore, Grp(complement));
        Formula identity = F.Id("I");

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("InnerProductSpace")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, space, Close,
            CloseBracket, Comma, Esc,
            subspace, Colon, Sp, Operatorname, Grp(F.Id("ClosedSubmodule")), Underscore,
            Grp(scalar), Open, space, Close, Comma, Esc,
            complementProjection, Sp, Eq, Sp, identity, Sp, Minus, Sp, projection,
            Sp, Land, Sp,
            projection, Sp, Circ, Sp, projection, Sp, Eq, Sp, projection,
            Sp, Land, Sp,
            complementProjection, Sp, Circ, Sp, complementProjection, Sp, Eq, Sp,
            complementProjection, Sp, Land, Sp,
            projection, Sp, Circ, Sp, complementProjection, Sp, Eq, Sp, D(0),
            Sp, Land, Sp,
            complementProjection, Sp, Circ, Sp, projection, Sp, Eq, Sp, D(0),
            Sp, Land, Sp,
            projection, Sp, Plus, Sp, complementProjection, Sp, Eq, Sp, identity, Dot));
    }
}
