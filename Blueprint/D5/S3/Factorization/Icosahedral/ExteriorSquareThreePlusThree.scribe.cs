using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Icosahedral;

internal sealed class ExteriorSquareThreePlusThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real exterior square of the centered A5 representation is two conjugate threes.",
        H("The Icosahedral Exterior-Square Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-icosahedral-summand-has-dimension-three"),
                DeclarationHandle.Create(Prefix + "V3_finrank"),
                H("The positive Hodge eigenspace has dimension three"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("finrank"), Open, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("V"), Underscore, D(3), Close, Sp, Eq, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The last three wedge coordinates form an explicit linear chart from the "
                    + "positive square-root-of-five Hodge eigenspace to real three-space."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("negative-icosahedral-summand-has-dimension-three"),
                DeclarationHandle.Create(Prefix + "V3Prime_finrank"),
                H("The negative Hodge eigenspace has dimension three"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("finrank"), Open, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("V"), Underscore, D(3), Apos, Close, Sp, Eq, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conjugate eigenbasis gives an explicit chart from the negative "
                    + "square-root-of-five Hodge eigenspace to real three-space."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("positive-icosahedral-summand-is-irreducible"),
                DeclarationHandle.Create(Prefix + "V3_irreducible"),
                H("The positive icosahedral summand is irreducible"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Irreducible"), Open, F.Id("A"), Underscore, D(5), Comma, Sp,
                    F.Id("V"), Underscore, D(3), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An exact orbit-frame certificate shows that every nonzero orbit spans "
                    + "all three coordinates, excluding a proper nonzero subrepresentation."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("negative-icosahedral-summand-is-irreducible"),
                DeclarationHandle.Create(Prefix + "V3Prime_irreducible"),
                H("The negative icosahedral summand is irreducible"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Irreducible"), Open, F.Id("A"), Underscore, D(5), Comma, Sp,
                    F.Id("V"), Underscore, D(3), Apos, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugating the integral quadratic frame certificate gives the same "
                    + "orbit-spanning argument for the negative eigenspace."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("icosahedral-threes-are-galois-conjugate"),
                DeclarationHandle.Create(Prefix + "V3_V3Prime_galois_conjugate"),
                H("The two icosahedral summands are Galois conjugate"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Q5GaloisConjugate"), Open,
                    F.Id("V"), Underscore, D(3), Comma, Sp,
                    F.Id("V"), Underscore, D(3), Apos, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both coordinate actions come from one exact matrix family over Q(sqrt 5): "
                    + "the two real actions use the embeddings sending sqrt 5 to plus or minus "
                    + "the positive real square root."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("exterior-square-is-product-of-icosahedral-threes"),
                DeclarationHandle.Create(Prefix + "exteriorSquareV4_equiv_V3_prod_V3Prime"),
                H("The exterior square is equivariantly the product of the two threes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lambda, Caret, Grp(D(2)), Sp, F.Id("V"), Underscore, D(4), Sp,
                    Equiv, Sp, F.Id("V"), Underscore, D(3), Sp, Times, Sp,
                    F.Id("V"), Underscore, D(3), Apos))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Spectral projectors for the reused Hodge matrix give an explicit linear "
                    + "equivalence, and commutation with every A5 action makes it equivariant."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("full-icosahedral-exterior-square-decomposition"),
                DeclarationHandle.Create(Prefix + "exteriorSquareV4_three_plus_three"),
                H("The full exterior-square decomposition theorem"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lambda, Caret, Grp(D(2)), Sp, F.Id("V"), Underscore, D(4), Sp,
                    Equiv, Sp, F.Id("V"), Underscore, D(3), Sp, Times, Sp,
                    F.Id("V"), Underscore, D(3), Apos, Comma, RowBreak,
                    F.Id("dim"), Sp, Eq, Sp, D(3), Comma, Sp,
                    F.Id("irreducible"), Comma, Sp, F.Id("GaloisConjugate")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This assembles the equivariant split, both dimension statements, both "
                    + "irreducibility results, and the typed Q(sqrt 5) conjugacy witness. The "
                    + "identity action and zero vector are checked as degenerate probes; the "
                    + "degree is fixed at two, so no empty-index or degree-zero input remains."))),
                DescribeRole.Theorem
            )),
        []));
}
