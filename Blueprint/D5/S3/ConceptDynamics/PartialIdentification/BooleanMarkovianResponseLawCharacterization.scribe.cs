using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class BooleanMarkovianResponseLawCharacterizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/BooleanMarkovianResponseLawCharacterization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized nonnegative law on Bool x Bool is a product of two "
            + "coordinate laws exactly when its two-by-two determinant vanishes.",
        H("Boolean Markovian Response Law Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-markovian-iff-determinant-zero"),
                DeclarationHandle.Create(
                    Prefix + "boolean_markovian_iff_determinant_zero"),
                H("Product structure is exactly determinant vanishing"),
                StatementSource.FromAuthor(DeterminantZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Necessity is the product determinant identity. For "
                            + "sufficiency, the two coordinate marginals are taken; "
                            + "normalization and the determinant equation show cell "
                            + "by cell that their product reconstructs the law.")),
                    Paragraph(Text(
                        "This is the two-mode boundary case of the partial "
                            + "identification programme: independence of a joint "
                            + "Boolean response law is a single polynomial "
                            + "constraint on its four masses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DeterminantZeroFormula()
    {
        Formula law = F.Id("P");
        Formula tt = Seq(law, Open, F.Id("tt"), Close);
        Formula ff = Seq(law, Open, F.Id("ff"), Close);
        Formula tf = Seq(law, Open, F.Id("tf"), Close);
        Formula ft = Seq(law, Open, F.Id("ft"), Close);
        return Disp(Seq(
            Forall, Sp, law, Comma, Sp,
            Call("isMarkovianTwoComponentLaw", law), Sp, Iff, Sp,
            tt, Sp, Cdot, Sp, ff, Sp, Eq, Sp, tf, Sp, Cdot, Sp, ft, Dot));
    }
}
