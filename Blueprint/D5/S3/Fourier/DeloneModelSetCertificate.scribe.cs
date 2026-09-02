using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DeloneModelSetCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit separation and covering certificates promote a cut-and-project "
            + "model set to Mathlib's bundled DeloneSet.",
        H("Delone Model-Set Certificates"),
        Blocks(Describe.Lean(
            DescribeId.Create("metric-certificates-are-equivalent-to-a-delone-structure"),
            DeclarationHandle.Create(
                "D5/S3/Fourier/DeloneModelSetCertificate.certificate_nonempty_iff_deloneSet_exists"),
            H("Metric certificates are equivalent to a Delone structure on the model-set carrier"),
            StatementSource.FromAuthor(EquivalenceFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A certificate stores a positive packing radius with separation and a positive covering radius with a cover of the full physical space.")),
                Paragraph(Text(
                    "These fields are exactly the data expected by Mathlib's canonical Delone.DeloneSet structure.")),
                Paragraph(Text(
                    "The equivalence keeps the topological burden explicit. A bounded internal window alone does not manufacture a Delone theorem; specialized model sets must supply the two metric witnesses."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Fourier/CutProjectScheme")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula EquivalenceFormula() => Disp(Seq(
        Call("Nonempty", Call("Certificate", F.Id("S"), F.Id("W"))),
        Sp, Iff, Sp, Exists, Sp, F.Id("D"), Comma, Sp,
        Call("carrier", F.Id("D")), Sp, Eq, Sp,
        Call("modelSet", F.Id("S"), F.Id("W"))));
}
