using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.QuadraticFields;

internal sealed class QuadraticOrderGeneratorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral generator has its actual quadratic minimal polynomial. Its basis spans the whole maximal order, so the Kummer-Dedekind index is one. This index condition is proved, not assumed when computing rational-prime splitting.", H("QuadraticOrderGenerator"), Blocks(
            Paragraph(Text("The integral generator has its actual quadratic minimal polynomial. Its basis spans the whole maximal order, so the Kummer-Dedekind index is one. This index condition is proved, not assumed when computing rational-prime splitting.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticordergenerator-orderpolynomial"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderPolynomial"), H("orderPolynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The defining polynomial of the coordinate generator of an integer quadratic algebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticordergenerator-ordergenerator-minpoly"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderGenerator_minpoly"), H("orderGenerator_minpoly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two coordinate basis vectors prove minimality over the integers themselves."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticordergenerator-integralgenerator"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator"), H("integralGenerator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The half-integral generator in the actual ring of integers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticordergenerator-integralgenerator-exponent"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_exponent"), H("integralGenerator_exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The maximality theorem discharges the exponent condition of Kummer-Dedekind at every rational prime, rather than leaving an assumed index-coprimality condition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticordergenerator-integralgenerator-minpoly"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_minpoly"), H("integralGenerator_minpoly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Its integer minimal polynomial is X squared minus X plus (p+1)/4."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal"))]));
}
