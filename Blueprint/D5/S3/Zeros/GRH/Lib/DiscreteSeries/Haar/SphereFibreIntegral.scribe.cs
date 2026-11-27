using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class SphereFibreIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sphere Fibre Integral", H("Sphere Fibre Integral"),
        Blocks(
            Paragraph(Text("Integrating one row and column of the Cayley density gives sphere volume.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SphereFibreIntegral.lintegral_cayleyDensity_skewColumnEquiv"),
                H("lintegral_cayleyDensity_skewColumnEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For J = 1, integrating Cayley's density cayleyDensity over the coordinates θ of row and column k₀, the complementary block η being fixed, gives 2πⁿ/(n−1)! times the density of η in size n−1; both sides are divided by 2πⁿa/(n−1)!, a > 0.")))))));
}
