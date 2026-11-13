using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class UniqueConfirmationDensityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/UniqueConfirmationDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common limit of original states and effects determines exclusion-label limits without assuming that the pure-state carrier is closed.",
        H("Original unique-confirmation density"), Blocks(
        Paragraph(Text("The carrier is a finite dimensional real normed space V, C is the same closed pointed generating cone, and u is strictly positive on each nonzero cone vector. K is the entire normalized base, P all its extreme points, and the effects are all linear functionals between zero and u on the entire cone. Every full exclusion has an injective affine chart of a positive dimensional closed Euclidean ball. The exclusion map on original pure labels is injective. No Pair premise, closedness of P, continuous ball family, common inner product, retraction or matrix representation is assumed.")),
        Describe.Lean(DescribeId.Create("unique-confirmer"), DeclarationHandle.Create(Owner + "UniqueConfirmer"),
            H("The complete original confirming-effect fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There exists an original proper effect e confirming p and vanishing on every state of the entire exclusion D(p); every original proper confirming effect with the same whole-face zero property equals e. This is uniqueness in the effect fiber and is distinct from uniqueness of the pure label associated with D(p)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-label-tendsto"), DeclarationHandle.Create(Owner + "original_label_tendsto"),
            H("Convergence of the entire original label sequence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fix any original pure p and x in the relative interior of its entire exclusion. For any sequence of original pure labels p(n) and any sequence x(n) in their respective exclusions, convergence of x(n) to x implies convergence of the full sequence p(n) to p. The points x(n) need not themselves lie in relative interiors, and their labels need not have unique confirmers.")),
                Paragraph(Text("For every subsequence, compactness of the whole original base and the whole effect interval gives a common further subsequence of actual label states and actual whole-exclusion confirming effects. Its state limit s initially belongs only to K. Joint continuity of evaluation gives e(s)=1 and e(x)=0. Nonnegativity at the relative interior point forces e to vanish on the entire original D(p). The original one-value-face theorem, full-ball maximality and the given injectivity force s=p. The subsequence criterion then yields convergence of the entire label sequence; purity of a cluster point is derived from the whole one-value face."))), DescribeRole.Theorem),
        Paragraph(Text("The density assertion additionally requires actual nearby contacts whose entire positive support cones are rays, exclusion of pure contacts, and normalization to singleton confirming-effect fibers. The label-limit theorem supplies the convergence step once such contacts have been constructed; it does not by itself assert the existence of those contacts, density, openness of the unique-confirmation locus, or closedness of P. These are conditional mathematical results about the specified original model, without a compiled realization of the full three-ball model or any physical interpretation claim.")))));
}
