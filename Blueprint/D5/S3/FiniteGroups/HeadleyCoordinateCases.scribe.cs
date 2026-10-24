using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyCoordinateCasesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exhaustive coordinate cases", H("The exhaustive coordinate cases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-coordinatecases-positiveequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateCases.positiveEquiv"),
                H("Remove only trivial factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restriction to the positive exponents is an additive equivalence because every omitted factor is ZMod 1. No assertion about its underlying prime is needed."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-coordinatecases-elementarycoordinates"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateCases.elementaryCoordinates"),
                H("Elementary coordinates use the field orbit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every positive exponent is one and two distinct positive entries exist, the positive-coordinate product has rank at least two. The finite-field cycle therefore transfers to the original coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-coordinatecases-twocoordinatesequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateCases.twoCoordinatesEquiv"),
                H("The two-factor leaf type"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If all exponents except two are zero, evaluation at the two selected entries identifies the entire group with their two cyclic factors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-coordinatecases-recursive-pair"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateCases.recursive_pair"),
                H("Two positive factors survive the reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Outside the elementary and two-factor minimum-one cases, choose an exponent at least two and another positive exponent. A third positive coordinate, when present, survives untouched. If only two positive coordinates exist, both exponents are at least two and both remain positive after reduction."))), DescribeRole.Theorem))));
}
