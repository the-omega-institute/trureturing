using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KilbasSaigo;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/boudabsasimon2021kilbassaigo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kilbas-Saigo series and hyperbolic bounds on the negative real axis.",
        H("The real Kilbas-Saigo function"), Blocks(
            Entry("kilbas-saigo-coefficient", "ksCoeff", "Gamma product coefficients",
                "The coefficient of order n is the product, for k from zero to n minus one, of Gamma(1+alpha(k m+l)) divided by Gamma(1+alpha(k m+l+1)). The empty product is one."),
            Entry("kilbas-saigo-function", "kilbasSaigo", "The defining real series",
                "For real parameters alpha, m, l and real argument z, the function is the sum over natural n of the coefficient of order n times z to the power n."),
            Entry("kilbas-saigo-claim", "claim", "Two hyperbolic bounds",
                "For 0<alpha<=1, m>0, l>m-1/alpha and x>=0, the value at -x lies between 1/(1+Gamma(1+alpha(l-m))/Gamma(1+alpha(l-m+1)) times x) and 1/(1+Gamma(1+alpha l)/Gamma(1+alpha(1+l)) times x)."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KilbasSaigo/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
