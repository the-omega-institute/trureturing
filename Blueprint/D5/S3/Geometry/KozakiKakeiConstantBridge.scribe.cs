using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiConstantBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiConstantBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The roots over distinct complex coordinates suffice to recover the signed matching polynomial up to a nonzero scalar.",
        H("From admissible constant matrices to a polynomial identity"),
        Blocks(
            Theorem("F_ne_zero", "Nonzero signed polynomial",
                "The first-coordinate coefficient is nonzero in each of the two size ranges.",
                FNeZero()),
            Theorem("affine_polynomial_scalar", "Scalar rigidity on the injective zero locus",
                "Use the linear root to remove the first coordinate wherever the coefficient and collision factors are nonzero. Polynomial evaluation then gives the cross-multiplied identity. Relative primeness gives polynomial divisibility, and equality of total degrees makes the quotient a nonzero scalar.",
                AffinePolynomialScalar()),
            Theorem("admissible_constant_matrix_scalar", "The constant-matrix bridge",
                "Preservation on all admissible rational-function matrices yields the scalar identity by applying the affine zero-locus argument to the admissible constant matrices.",
                AdmissibleConstantMatrixScalar()))));

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula FNeZero() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, F.Id("m"), Sp, Neq, Sp, D(3), Sp, Implies, Sp, F.Id("F"), Open, F.Id("m"),
        Close, Sp, Neq, Sp, D(0));

    private static Formula AffinePolynomialScalar() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, D(2), Sp, Le,
        Sp, F.Id("m"), Sp, Implies, Sp, F.Id("m"), Sp, Neq, Sp, D(3), Sp, Implies, Sp, Open, Forall, Sp,
        F.Id("t"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))),
        Comma, Sp, Word("Injective"), Open, F.Id("t"), Close, Sp, Implies, Sp, Word("eval"), Open, F.Id("t"),
        Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Eq, D(0), Sp, Implies, Sp, Word("eval"), Open,
        F.Id("t"), Comma, Word("rename"), Open, F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close,
        Close, Eq, D(0), Close, Sp, Implies, Sp, Open, Exists, Sp, F.Id("c"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("C"))), Comma, Sp, F.Id("c"), Sp, Neq, Sp, D(0), Sp, Land, Sp, Word("rename"), Open,
        F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Sp, Eq, Sp, F.Id("C"), Open, F.Id("c"),
        Close, Sp, Cdot, Sp, F.Id("F"), Open, F.Id("m"), Close, Close);

    private static Formula AdmissibleConstantMatrixScalar() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, D(2), Sp, Le,
        Sp, F.Id("m"), Sp, Implies, Sp, F.Id("m"), Sp, Neq, Sp, D(3), Sp, Implies, Sp, Word("PreservesLevel"),
        Open, F.Id("s"), Close, Sp, Implies, Sp, Open, Exists, Sp, F.Id("c"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("C"))), Comma, Sp, F.Id("c"), Sp, Neq, Sp, D(0), Sp, Land, Sp, Word("rename"), Open,
        F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Sp, Eq, Sp, F.Id("C"), Open, F.Id("c"),
        Close, Sp, Cdot, Sp, F.Id("F"), Open, F.Id("m"), Close, Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-constantbridge-" + name.ToLowerInvariant().Replace('_', '-');
}
