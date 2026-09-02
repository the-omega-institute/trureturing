using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GoldenCutProjectSchemeAdapterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing golden Minkowski lattice instantiates the generic "
            + "cut-and-project carrier without changing its model sets.",
        H("Golden Cut-and-Project Adapter"),
        Blocks(Describe.Lean(
            DescribeId.Create("the-generic-and-existing-golden-model-sets-coincide"),
            DeclarationHandle.Create(
                "D5/S3/Fourier/GoldenCutProjectSchemeAdapter.goldenScheme_modelSet_eq"),
            H("The generic and existing golden model sets coincide"),
            StatementSource.FromAuthor(AgreementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The lattice carrier is the existing range of the two real golden embeddings.")),
                Paragraph(Text(
                    "Injectivity of physical projection follows from injectivity of the distinguished real embedding on GoldenInt.")),
                Paragraph(Text(
                    "Unfolding a lattice-range witness identifies the generic internal-window selection with the repository's established modelSet predicate. The existing object therefore becomes the consumer of the shared cut-and-project API."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Scale/MinkowskiModelSet")),
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

    private static Formula AgreementFormula() => Disp(Seq(
        Call("modelSet", Call("goldenScheme"), F.Id("W")),
        Sp, Eq, Sp,
        Seq(Operatorname, Grp(F.Id("modelSet")), Underscore,
            Grp(Seq(Mathrm, Grp(F.Id("golden")))), Open, F.Id("W"), Close)));
}
