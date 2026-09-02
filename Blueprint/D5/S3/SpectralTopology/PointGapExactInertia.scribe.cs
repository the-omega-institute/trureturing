using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class PointGapExactInertiaDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/PointGapExactInertia.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite point gap gives exact half-dimensional chiral inertia.",
        H("Point-Gap Exact Inertia"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("point-gap-localizer-exact-inertia"),
                DeclarationHandle.Create(
                    Prefix + "zero_scale_localizer_inertia_of_point_gap"),
                H("Point-gap exact zero-scale inertia"),
                StatementSource.FromAuthor(ExactInertiaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive and negative inertia counts of a finite Hermitian matrix add to its rank, and a finite point gap gives the zero-scale localizer full rank on the doubled carrier.")),
                    Paragraph(Text(
                        "Combined with the frozen chiral inertia balance, the positive and negative zero-scale counts therefore both equal the original carrier cardinality: under a point gap there are no zero modes, and the doubled finite spectrum splits into equally many positive and negative eigenvalues."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FiniteSpectralLocalizer")),
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

    private static Formula ExactInertiaFormula() => Disp(Seq(
        Call("posIndex", Call("localizerZero", F.Id("X"), F.Id("H"), F.Id("x"), F.Id("z"))),
        Sp, Eq, Sp, Call("card", F.Id("n")),
        Sp, Land, Sp,
        Call("negIndex", Call("localizerZero", F.Id("X"), F.Id("H"), F.Id("x"), F.Id("z"))),
        Sp, Eq, Sp, Call("card", F.Id("n"))));
}
