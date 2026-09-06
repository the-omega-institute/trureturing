using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateSecondDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintCertificateSecond.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact LDL factorizations for sixteen numerical branch matrices.",
        H("Ququint Certificate Second Half"),
        Blocks([
            Paragraph(Text("Each displayed identity uses branch from "
                + "D5.S3.Quantum.Magic.QuquintCertificateData and the public "
                + "lower and pivot declarations named in that identity. "
                + "These are certificates for explicit numerical matrices. "
                + "QuquintCertificateBridge identifies their data with the phase-point "
                + "forms of QuquintWignerCriticalGeometry.")),
            .. Enumerable.Range(16, 16).SelectMany(index => Certificate(index, Num(index)))])));

    private static DocumentBlock[] Certificate(int index, Formula numeral) =>
    [
        Definition($"lower{index}", $"Unit-lower factor for branch {index}",
            Seq(Name("Matrix"), Sp, Parenthesized(Seq(Name("Fin"), Sp, D(4))), Sp,
                Parenthesized(Seq(Name("Fin"), Sp, D(4))), Sp, RealType),
            "The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, "
                + "entries above the diagonal zero, and six rational-polynomial entries in "
                + "QuquintCertificateData.radical below the diagonal."),
        Definition($"pivots{index}", $"Pivots for branch {index}",
            Seq(Name("Fin"), Sp, D(4), To, RealType),
            "The four ordered quartic-field entries are the explicit pivot vector in Lean. "
                + "The corresponding ldl identity uses them in this order; positivity is proved in "
                + "QuquintCertificateAssembly."),
        Describe.Lean(
        DescribeId.Create($"ququint-ldl-{index}"),
        DeclarationHandle.Create(Module + $"ldl_{index}"),
        H($"Branch {index}"),
        StatementSource.FromAuthor(Disp(Seq(
            Minus, Branch, Parenthesized(Seq( numeral)), Eq,
            Name($"lower{index}"), Cdot, Name("Matrix"), Dot, Name("diagonal"),
            Parenthesized(Seq( Name($"pivots{index}"))), Cdot,
            Name("Matrix"), Dot, Name("transpose"), Parenthesized(Seq( Name($"lower{index}")))))),
        AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("Exact arithmetic using radical_quartic verifies "
            + "every entry of the factorization. The matrices and pivots are "
            + "the public Lean declarations in this module; no positivity "
            + "claim is inferred from the factorization alone."))),
        DescribeRole.Theorem)
    ];

    private static DocumentBlock Definition(string name, string title, Formula type, string explanation) =>
        Describe.Lean(DescribeId.Create("ququint-factor-" + name),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(Seq(Name(name), Colon, type))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Branch => Seq(Name("D5"), Dot, Name("S3"), Dot,
        Name("Quantum"), Dot, Name("Magic"), Dot, Name("QuquintCertificateData"),
        Dot, Name("branch"));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
