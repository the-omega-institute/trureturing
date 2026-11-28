using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ResidueRings;

internal sealed class MesyanIdempotentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/ResidueRings/MesyanIdempotent";
    private const string Criterion =
        "D5/S3/Arith/ResidueRings/MesyanCancellative.product_unit_iff_eq_cyclicPreservingMultipliers";
    private const string Source = "D5/L/ArithUnits/mesyan2026quantales";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The additively idempotent case of Mesyan's Question 36.",
        H("Units of additive-submonoid products with idempotent addition"),
        Blocks(
            Paragraph(Text("Use the product from Definition 4, so elements of the product are positive finite "
                + "sums of pairwise products with factors in the specified submonoids. The theorem uses "
                + "two-sided identity laws for this binary operation, which are meaningful even when "
                + "multiplication is nonassociative. "), Ref(Source), Text(".")),
            Describe.Lean(
                DescribeId.Create("mesyan-question-36-idempotent-classification"),
                DeclarationHandle.Create(Module + ".product_unit_iff"),
                H("Classification for additively idempotent semirings"),
                StatementSource.FromAuthor(ClassificationStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Source)),
                Blocks(
                    Paragraph(Text("Idempotent addition reduces the cyclic additive submonoid of x to {0, x}. "
                        + "By the "), Ref(Criterion), Text(", a product unit is the submonoid C of "
                        + "cyclic-preserving multipliers, and each element has a left and right fixer in C. "
                        + "For e and f in C, a nonzero product ef must equal both e and f. "
                        + "Applying this to a left fixer of a nonzero e in C gives e² = e.")),
                    Paragraph(Text("If distinct nonzero elements e and f belong to C, then ef and fe are zero. "
                        + "Distributivity gives (e + f)e = e and (e + f)f = f. Both products are nonzero, "
                        + "forcing e + f to equal e and f. Thus C has at most one nonzero element. "
                        + "If the semiring has a nonzero element, its fixer supplies that unique multiplier. "
                        + "Every nonzero element has this same fixer on each side, and it fixes zero by "
                        + "the zero multiplication laws. In the zero semiring, zero is a two-sided identity.")),
                    Paragraph(Text("Conversely, a global two-sided identity belongs to C and fixes every "
                        + "element on both sides. The criterion then gives a unit for the binary product."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Id("R");

    private static Formula Parens(Formula body) => Seq(Open, body, Close);

    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula UnitLaws(Formula unit, Formula element) =>
        Seq(Equal(Product(unit, element), element), Sp, Land, Sp, Equal(Product(element, unit), element));

    private static Formula ClassificationStatement()
    {
        Formula a = F.Id("a");
        Formula idempotent = Bind(Forall, "a", R, Equal(Seq(a, Sp, Plus, Sp, a), a));
        Formula submonoids = Seq(F.Id("AddSubmonoid"), Sp, R);
        Formula productUnit = Bind(Exists, "E", submonoids,
            Bind(Forall, "M", submonoids, UnitLaws(F.Id("E"), F.Id("M"))));
        Formula identity = Bind(Exists, "u", R, Bind(Forall, "x", R, UnitLaws(F.Id("u"), F.Id("x"))));
        return Disp(Bind(Forall, "R", F.Id("Type"),
            Seq(OpenBracket, F.Id("NonUnitalNonAssocSemiring"), Sp, R, CloseBracket, Comma, Sp,
                Parens(idempotent), Sp, Rightarrow, Sp,
                Parens(Seq(Parens(productUnit), Sp, Leftrightarrow, Sp, Parens(identity))))));
    }
}
