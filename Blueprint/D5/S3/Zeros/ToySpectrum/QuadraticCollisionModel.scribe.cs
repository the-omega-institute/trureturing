using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class QuadraticCollisionModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic collision model has explicit real, double, and conjugate roots, and always has two roots with multiplicity.",
        H("Quadratic Collision Model"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-collision-model-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel."
                    + "quadratic_collision_model_certificate"),
                H("The z squared plus t model has the three root regimes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("t"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Open,
                    Open, Open, F.Id("t"), Sp, Lt, Sp, D(0), Close, Sp, Rightarrow, Sp, Open,
                    Operatorname, Grp(F.Id("roots")), Open,
                    Operatorname, Grp(F.Id("quadraticCollisionPolynomial")), Open, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, OpenBrace, Sqrt, Grp(Open, Minus, Sp, F.Id("t"), Close),
                    Comma, Sp, Minus, Sp, Sqrt, Grp(Open, Minus, Sp, F.Id("t"), Close), CloseBrace,
                    Sp, Land, Sp, Sqrt, Grp(Open, Minus, Sp, F.Id("t"), Close),
                    Sp, Neq, Sp, Minus, Sp, Sqrt, Grp(Open, Minus, Sp, F.Id("t"), Close),
                    Close, Close,
                    Close, Sp, Land, Sp,
                    Open, Open, F.Id("t"), Sp, Eq, Sp, D(0), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("roots")), Open,
                    Operatorname, Grp(F.Id("quadraticCollisionPolynomial")), Open, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, OpenBrace, D(0), Comma, D(0), CloseBrace, Close,
                    Sp, Land, Sp,
                    Open, Open, D(0), Sp, Lt, Sp, F.Id("t"), Close, Sp, Rightarrow, Sp, Open,
                    Operatorname, Grp(F.Id("roots")), Open,
                    Operatorname, Grp(F.Id("quadraticCollisionPolynomial")), Open, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, OpenBrace, F.Id("i"), Sp, Sqrt, Grp(F.Id("t")), Comma,
                    Minus, Sp, F.Id("i"), Sp, Sqrt, Grp(F.Id("t")), CloseBrace, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("conj")), Open, F.Id("i"), Sp, Sqrt, Grp(F.Id("t")), Close,
                    Sp, Eq, Sp, Minus, Sp, F.Id("i"), Sp, Sqrt, Grp(F.Id("t")),
                    Close, Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t < 0 the roots are the distinct real numbers plus or minus square root of minus t. "
                    + "At t = 0 the root multiset is the doubled zero. For t > 0 the roots are the conjugate "
                    + "pair plus or minus i square root t. The certificate is for this explicit polynomial model "
                    + "only; it does not assert a zeta zero theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-zeros-born-in-pairs-not-created"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel."
                    + "off_line_zeros_born_in_pairs_not_created"),
                H("The quadratic model always has two roots with multiplicity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("t"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("roots")), Open,
                    Operatorname, Grp(F.Id("quadraticCollisionPolynomial")), Open, F.Id("t"), Close, Close, Close,
                    Sp, Eq, Sp, D(2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The multiset cardinality is two for every real t, including the collision point where "
                    + "the two entries coincide. Thus the off-line conjugate pair in this toy model is a "
                    + "redistribution of two roots through a double root, not creation of additional roots."))),
                DescribeRole.Theorem)),
        []));
}
