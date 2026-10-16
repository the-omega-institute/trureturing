using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalPhysicalNonlocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original EJM certificate excludes continuous triangle locality in an explicit region of physical independent-source noise.",
        H("Physical noise robustness of the original EJM distribution"),
        Blocks(
            Paragraph(Text("Each of the three independent sources is the convex mixture of the singlet and white noise, with its own visibility x, y or z in [0,1]. The local measurements are the actual elegant joint measurements. The function ejmProbability is their Born probability, as proved in ElegantJointMeasurementSourceNoise; it is not an output mixture substituted for source noise.")),
            Paragraph(Text("The excluded region is (1-x)+(1-y)+(1-z) < 2329145/146036723916865536. This threshold is strictly positive. In particular it contains the ideal point (1,1,1) and the box in which every visibility exceeds 1 - 2329145/438110171750596608 and is at most 1. These are sufficient regions; no optimal threshold is asserted.")),
            Describe.Lean(
                DescribeId.Create("local-law-in-region"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("A local law inside the physical noise region"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed claim asserts that some physical visibilities x, y and z satisfy the strict total-deficit bound and that their actual EJM law is triangle-local. IsTriangleLocal quantifies over measurable response kernels with hidden variables on three independent copies of [0,1]; it does not restrict the hidden variables to a finite set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("no-local-law-in-region"),
                DeclarationHandle.Create(Prefix + "result"),
                H("No continuous triangle-local realization in the region"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof uses the original full twenty-coordinate, four-outcome score with all sixteen triangle and sixteen singleton blocks. Its complete frontier root supplies the integer margin 6987435 without any acceptance hypothesis. A kernel check of all 4,588 literal triangle coefficient nodes gives the amplitude bound 53480245575024, including every lookup and the default zero value.")),
                    Paragraph(Text("The existing analytic noise theorem bounds a local score expectation by 8192 times that amplitude times the sum of the three visibility deficits. Below the displayed rational threshold this is strictly less than the earned global margin, a contradiction. The root and the numerical amplitude are live dependencies of this proof and first freeze with it; merely preparing these sources establishes no acceptance.")),
                    Paragraph(Text("On [0,1]^3, the existing triangle_noise_distribution theorem for the same three singlet/white-noise sources and the same EJM measurements proves nonnegativity and total mass one. The refutation therefore applies to physical probability laws throughout the region."))),
                DescribeRole.Theorem))));
}
