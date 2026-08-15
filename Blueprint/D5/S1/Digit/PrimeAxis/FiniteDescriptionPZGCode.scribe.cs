using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class FiniteDescriptionPzgCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifted prime-sequence description codes embed into canonical PZG tables.",
        H("Finite Description Codes in PZG Tables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-description-pzg-code-specification"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PrimeAxis/FiniteDescriptionPZGCode."
                    + "finite_description_pzg_code_spec"),
                H("Finite description codes have canonical PZG tables"),
                StatementSource.FromAuthor(DescriptionCodeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite description is represented here by a finite sequence of "
                        + "natural numbers. Its shifted prime-power code is always positive, "
                        + "including for the empty description, and therefore lies in the "
                        + "positive-natural codomain of the established primeAxisEncoding "
                        + "equivalence.")),
                    Paragraph(Text(
                        "Applying the inverse equivalence produces a canonical PrimeAxisTable. "
                        + "The forward equivalence returns exactly the original shifted "
                        + "prime-sequence code, and decodePrimeAxisTable recovers its underlying "
                        + "natural number.")),
                    Paragraph(Text(
                        "This theorem supplies only the generic PZG membership bridge. It does "
                        + "not assert a kernel self-code fixed point: the repository does not "
                        + "yet define a particular kernel, its finite syntax description, or a "
                        + "kernel self-code operator."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/History/PrimeSequenceCode")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/Digit/PrimeAxisEncoding"))]));

    private static Formula DescriptionCodeFormula()
    {
        Formula description = F.Id("D");
        Formula tableCode = Seq(
            Operatorname, Grp(F.Id("finiteDescriptionPZGCode")),
            Open, description, Close);
        Formula primeCode = Seq(
            Operatorname, Grp(F.Id("primeSequenceCode")),
            Open, description, Close);
        Formula positivePrimeCode = Seq(
            Operatorname, Grp(F.Id("positivePrimeSequenceCode")),
            Open, description, Close);
        return Disp(Seq(
            Forall, Sp, description, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("N")), Close,
            Comma, Esc,
            Operatorname, Grp(F.Id("primeAxisEncoding")), Open, tableCode, Close,
            Sp, Eq, Sp, positivePrimeCode, Sp, Land, Sp,
            Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, tableCode, Close,
            Sp, Eq, Sp, primeCode, Dot));
    }
}
