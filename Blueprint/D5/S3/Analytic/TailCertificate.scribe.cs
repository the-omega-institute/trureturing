using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class TailCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/TailCertificate",
            "Finite tail certificates add with summed budgets and enclose the exact sum at every window."),
        H("Finite Sums of Tail Certificates"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-tail-certificates-sum-and-enclose"),
                H("Finite tail certificates sum and enclose"),
                LeanTheorem(
                    "D5/S3/Analytic/TailCertificate."
                    + "finite_tail_certificates_sum_and_enclose"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("Controlled")), Open,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("b"), Underscore, Grp(F.Id("i")), Close,
                    Sp, Land, Sp,
                    Vert,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("v"), Underscore, Grp(F.Id("i")),
                    Minus,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("r"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close,
                    Vert, Le,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("b"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("r"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close,
                    Minus,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("b"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close,
                    Le,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("v"), Underscore, Grp(F.Id("i")),
                    Le,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("r"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close,
                    Plus,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("s")),
                    F.Id("b"), Underscore, Grp(F.Id("i")), Open, F.Id("W"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For a finite family of certificates, the pointwise sum of their budget "
                    + "functions remains controlled. At every window W, the absolute difference "
                    + "between the sum of the exact values and the sum of the window readings is "
                    + "at most the sum of the window budgets. Equivalently, the exact sum lies in "
                    + "the closed interval from the summed reading minus the summed budget to the "
                    + "summed reading plus the summed budget.")))
            ))));
}
