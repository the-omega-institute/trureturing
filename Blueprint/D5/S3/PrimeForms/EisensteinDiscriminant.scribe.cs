using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class EisensteinDiscriminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/EisensteinDiscriminant",
            "Forms in V at discriminant 4k are in bijection with the Eisenstein representations of k."),
        H("Eisenstein Discriminant Representations"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("forms-biject-eisenstein-representations"),
                H("Forms at discriminant 4k biject with Eisenstein representations"),
                LeanTheorem(
                    "D5/S3/PrimeForms/EisensteinDiscriminant."
                    + "forms_biject_eisenstein_representations"),
                Disp(Seq(
                    Left, OpenBrace,
                    Open, F.Id("A"), Comma, F.Id("B"), Comma, F.Id("C"), Close,
                    InMacro, Mathbb, Grp(F.Id("Z")), Caret, Grp(D(3)), Mid, Sp,
                    F.Id("B"), Eq, Minus, D(2), Open, F.Id("A"), Plus, F.Id("C"), Close,
                    Comma, Sp, F.Id("B"), Caret, Grp(D(2)), Minus, D(4), F.Id("A"), F.Id("C"),
                    Eq, D(4), F.Id("k"),
                    Right, CloseBrace,
                    Sp, To, Sp,
                    Left, OpenBrace,
                    Open, F.Id("A"), Comma, F.Id("C"), Close,
                    InMacro, Mathbb, Grp(F.Id("Z")), Caret, Grp(D(2)), Mid, Sp,
                    F.Id("A"), Caret, Grp(D(2)), Plus, F.Id("A"), F.Id("C"), Plus,
                    F.Id("C"), Caret, Grp(D(2)), Eq, F.Id("k"),
                    Right, CloseBrace,
                    Comma, Quad,
                    Open, F.Id("A"), Comma, F.Id("B"), Comma, F.Id("C"), Close,
                    Mapsto, Open, F.Id("A"), Comma, F.Id("C"), Close,
                    Quad, F.Text, Grp(Sp, F.Id("is"), Sp, F.Id("bijective")), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For each integer k, a binary quadratic form with coefficients A, B, C "
                    + "lies in V when B = -2(A + C). Under that constraint its discriminant "
                    + "equals 4k exactly when A^2 + AC + C^2 = k. The coefficient projection "
                    + "sending the form to (A, C) is bijective, with inverse "
                    + "(A, C) |-> (A, -2(A + C), C). Thus the V-form incidence total and "
                    + "the Eisenstein representation number are identified by an explicit "
                    + "bijection, rather than only by a numerical equality.")))
            ))));
}
