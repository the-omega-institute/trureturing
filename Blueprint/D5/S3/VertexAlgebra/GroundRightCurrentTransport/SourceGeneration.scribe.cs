using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class SourceGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SourceGeneration",
        H("SourceGeneration"),
        Blocks(
            Paragraph(Text("The source is the original finitely supported charge family of oscillator polynomials. No charge generating set or positive definite form is assumed. A negative neutral mode with index -(n+1) multiplies the polynomial in its charge sector by X(i,n). Thus a monomial is produced by its occurrence word on the same charged ground.")),
            Paragraph(Text("Theta reverses the charge and negates every oscillator. The projection is one half times b plus its signed reflection. Projection across each negative current reverses the selected ground sign; the explicit finite expansion keeps the original charge support and each polynomial support independent.")),
            Paragraph(Text("The construction permits rank zero, zero charges and a vanishing minus sector. It uses no division by a charge and makes no finite-dimensionality claim. These are repository-derived consequences of the native source formulas and classical lattice involution calculus; no literature novelty or physical realization is asserted.")),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-sectorsign-not"),
                DeclarationHandle.Create(Prefix + "sectorSign_not"),
                H("Opposite source signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Negating the Bool sector negates its complex eigenvalue."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-sectorsign-square"),
                DeclarationHandle.Create(Prefix + "sectorSign_square"),
                H("Involutive source sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the two eigenvalues has square one, including when the associated eigenspace vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-wordparity-not"),
                DeclarationHandle.Create(Prefix + "wordParity_not"),
                H("Word parity and sign reversal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite word commutes with reversing its input sector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-theta-source-expansion"),
                DeclarationHandle.Create(Prefix + "theta_source_expansion"),
                H("Finite theta eigensource expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual source b and either sector, the projection is the double finite sum over b.support and each independent polynomial support. Its coefficient is the original oscillator coefficient, and its summand is the actual rightCurrentWord on a projected charged ground with the sign reversed once per letter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-sectorproject-eigen"),
                DeclarationHandle.Create(Prefix + "sectorProject_eigen"),
                H("Actual projection eigenvalue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theta projection has the selected eigenvalue on the original carrier, including its zero component."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-projectedground-eigen"),
                DeclarationHandle.Create(Prefix + "projectedGround_eigen"),
                H("Charged ground eigenvalue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The projected charge ground has the declared theta sign for every charge, including zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-rightcurrentword-eigen"),
                DeclarationHandle.Create(Prefix + "rightCurrentWord_eigen"),
                H("Current-word eigenvalue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each actual negative neutral current reverses the theta eigenvalue. The word has sector wordParity(word,epsilon)."))),
                DescribeRole.Theorem))));
}
