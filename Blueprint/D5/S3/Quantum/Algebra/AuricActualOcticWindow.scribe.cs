using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricActualOcticWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/AuricActualOcticWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual characteristic-zero octic field and its original eight embedding labels are retained for the 43.2 cut-free bridge.",
        H("Actual characteristic-zero octic embedding frame"),
        Blocks(
            Paragraph(Text(
                "The designated field is the intermediate field Q(2^(1/8)) inside C. "
                + "A second finite adjoining field carries a primitive eighth root and the eight original labels. "
                + "All quotient and denominator transport remains in the same actual field.")),
            Describe.Lean(
                DescribeId.Create("actual-octic-generator-minpoly"),
                DeclarationHandle.Create(Prefix + "aC_minpoly"),
                H("The designated octic generator"),
                StatementSource.FromAuthor(Disp(GeneratorFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive real eighth root has eighth power two, and its complex image has minimal "
                    + "polynomial X^8 - 2 over Q.  The adjoining source field is finite over Q."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("actual-octic-label-injectivity"),
                DeclarationHandle.Create(Prefix + "sigma_injective"),
                H("The eight original labels are distinct"),
                StatementSource.FromAuthor(Disp(LabelFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The primitive eighth root makes the eight label maps injectively indexed. "
                    + "The same common extension map transports every original quotient and preserves "
                    + "nonzero denominators."))),
                DescribeRole.Lemma)),
        [])));

    private static Formula GeneratorFormula() =>
        Seq(Call("minpoly", F.Id("ℚ"), F.Id("aC")), Eq, F.Id("octic"));

    private static Formula LabelFormula() =>
        Call("Function.Injective", F.Id("sigma"));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open,
            Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), Close);

}
