using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CutProjectSchemeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The algebraic core of a cut-and-project scheme produces model sets "
            + "functorially from internal windows.",
        H("Cut-and-Project Schemes"),
        Blocks(Describe.Lean(
            DescribeId.Create("model-sets-are-monotone-in-the-internal-window"),
            DeclarationHandle.Create(
                "D5/S3/Fourier/CutProjectScheme.scheme_modelSet_mono"),
            H("Model sets are monotone in the internal window"),
            StatementSource.FromAuthor(MonotoneFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A scheme stores an additive subgroup of physical times internal space and requires physical projection to be injective on its lattice carrier.")),
                Paragraph(Text(
                    "An internal window selects lattice points, whose physical projections form the model set.")),
                Paragraph(Text(
                    "Enlarging the window can only enlarge the selection, so the model-set construction is monotone; the same injectivity also makes it preserve binary window intersections."))),
            DescribeRole.Theorem))));

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

    private static Formula WindowOne() => Seq(F.Id("W"), Underscore, Grp(D(1)));

    private static Formula WindowTwo() => Seq(F.Id("W"), Underscore, Grp(D(2)));

    private static Formula MonotoneFormula() => Disp(Seq(
        WindowOne(), Sp, Subseteq, Sp, WindowTwo(),
        Sp, Implies, Sp,
        Call("modelSet", F.Id("S"), WindowOne()),
        Sp, Subseteq, Sp,
        Call("modelSet", F.Id("S"), WindowTwo())));
}
