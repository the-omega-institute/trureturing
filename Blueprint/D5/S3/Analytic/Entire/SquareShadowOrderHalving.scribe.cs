using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class SquareShadowOrderHalvingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Entire/SquareShadowOrderHalving.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circular maximum modulus is attained for continuous complex functions. "
            + "A square shadow rescales the radius and halves extended-real growth order.",
        H("Maximum modulus and square-shadow growth order"),
        Blocks(
            Result("maximum", "maxModulus", "Circular maximum modulus",
                "The definition is the real supremum of the image of the radius-r sphere "
                    + "under the norm of f. Continuity supplies boundedness; nonnegative "
                    + "radius supplies nonemptiness. Negative radii are irrelevant to growth order.",
                Eqn(M("f", F.Id("r")), Call("sSup", Call("normImageOfSphere", F.Id("f"),
                    F.Id("r")))), DescribeRole.Definition),
            Result("zero-radius", "max_modulus_zero", "Radius zero",
                "For every complex-valued function, the radius-zero sphere is the singleton "
                    + "origin, so its maximum modulus is the norm of the value there.",
                Eqn(M("f", Num(0)), Call("norm", Call("f", Num(0))))),
            Result("attainment", "max_modulus_attained", "The maximum is attained",
                "For continuous f and nonnegative r, there exists a complex z on the "
                    + "radius-r sphere whose value has norm maxModulus(f,r). This applies "
                    + "the compact extreme value theorem and identifies the attained value "
                    + "with the supremum.",
                Disp(Seq(Exists, Sp, F.Id("z"), Sp, InMacro, Sp,
                    Call("sphere", Num(0), F.Id("r")), Comma, Sp,
                    M("f", F.Id("r")), Sp, Eq, Sp, Call("norm", Call("f", F.Id("z")))))),
            Result("square-maximum", "max_modulus_square_shadow", "Square-shadow maximum modulus",
                "Assume F and G are continuous complex functions and F(z)=G(z squared) "
                    + "for every z. For every nonnegative r, their circular maxima satisfy "
                    + "the displayed equality. One inequality squares a maximizing point; "
                    + "the other chooses a complex square root of a maximizing point. "
                    + "Radius zero is included.",
                Eqn(M("G", F.Id("r")), M("F", Seq(Sqrt, Grp(F.Id("r"))))),
                literature: true),
            Result("order", "order", "Extended-real growth order",
                "The real quotient is coerced to EReal before taking the limsup at "
                    + "positive infinity. Thus positive infinity remains a possible order. "
                    + "Lean's total real logarithm and division define the expression at "
                    + "all small radii, including one; only the tail affects the limsup. "
                    + "Under these conventions the zero function has order zero.",
                Eqn(Call("order", F.Id("f")), Call("limsupAtTop",
                    Seq(Frac, Grp(Call("log", Call("log", M("f", F.Id("r"))))),
                        Grp(Call("log", F.Id("r")))))), DescribeRole.Definition,
                literature: true),
            Result("halving", "order_square_shadow", "Growth order is halved",
                "For the same continuous F and G satisfying F(z)=G(z squared), the "
                    + "extended-real orders obey this equality, including infinite order. "
                    + "The maximum-modulus equality, the logarithm of a square root, "
                    + "the image of atTop under square root, and positive scalar "
                    + "multiplication of limsup form one proof chain.",
                Eqn(Call("order", F.Id("G")), Seq(Frac, Grp(Call("order", F.Id("F"))),
                    Grp(Num(2)))), literature: true),
            Result("order-one", "order_half_of_order_one", "Order one descends to one half",
                "If F has order one, its square shadow G has order one half. In the "
                    + "entire-function setting, the source constructs G from the even "
                    + "Taylor coefficients of F. This module takes the resulting identity "
                    + "F(z)=G(z squared) as a hypothesis; it does not reconstruct the "
                    + "Taylor series or prove a canonical-product theorem.",
                Eqn(Call("order", F.Id("G")), Seq(Frac, Grp(Num(1)), Grp(Num(2)))),
                literature: true))));

    private static DocumentBlock Result(string id, string declaration, string title, string prose,
        Formula formula, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create("square-shadow-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Analytic/trureturing2026squareshadow"))
                : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula M(string f, Formula r) => Call("M", F.Id(f), r);
    private static Formula Eqn(Formula a, Formula b) => Disp(Seq(a, Sp, Eq, Sp, b));
}
