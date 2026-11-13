using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorNormalChartDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorNormalChart.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original regular confirmation yields the full signed normal restriction isomorphism and bounded three-dimensional coordinates.",
        H("Normal coordinates at an original regular anchor"), Blocks(
        Paragraph(Text("Let V be a finite dimensional real normed space, C its original closed generating cone, and u a linear functional strictly positive on every nonzero vector in C. Keep the entire normalized base K, all its extreme points P, and the entire original effect interval zero <= f <= u. Every original exclusion D(p) is the image of the entire closed Euclidean three-ball under an injective affine map. Assume that equality of exclusion sets implies equality of their original pure labels. No closedness of P, pair properness, least-confirmation law, matrix representation or dimension reduction is assumed.")),
        Describe.Lean(DescribeId.Create("three-space"), DeclarationHandle.Create(Owner + "ThreeSpace"),
            H("Original coordinate space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The coordinate space is EuclideanSpace over the reals indexed by Fin 3, with its Euclidean inner product and norm."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("full-ball-chart"), DeclarationHandle.Create(Owner + "FullBall3Chart"),
            H("Entire exclusion chart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A chart consists of an injective affine map a from the three-dimensional coordinate space to V whose image of the whole closed unit ball equals the original exclusion. Its center is c=a(0), and its linear part B is injective. The native chart conversion preserves the map and the exact whole-image equality."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("eb3"), DeclarationHandle.Create(Owner + "EB3"),
            H("All original exclusions are three-balls"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every pure point of the entire original base there exists a full three-ball chart. This quantifies every original label and every mixed state in its exclusion."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("native-chart"), DeclarationHandle.Create(Owner + "nativeChart"),
            H("Existing native chart carrier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The same affine map, injection and whole exclusion equality form an ExclusionChart with dimension exactly three."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("regular"), DeclarationHandle.Create(Owner + "Regular"),
            H("Original regularity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Regularity at p says that there exists exactly one original linear effect e confirming p and vanishing on every state of D(p). It is uniqueness in the entire common-confirmation family, rather than uniqueness of an exclusion label."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("normal-span"), DeclarationHandle.Create(Owner + "NormalSpan"),
            H("Signed original normal space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("N(p) is the existing zeroPositive set of all original linear functionals nonnegative on the whole cone and zero at p. NormalSpan is its real linear span. Neither positivity nor a choice of effects replaces this signed span."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coordinates"), DeclarationHandle.Create(Owner + "coordinates"),
            H("Actual constant and slope restriction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Restriction coordinates of f are its value at the chart center and the existing Euclidean Riesz slope of f composed with B. The exact native slope formula gives f(a(w))=f(c)+inner(slope(f),w) for every coordinate vector, including vectors outside the unit ball."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("affine-coordinates"), DeclarationHandle.Create(Owner + "affineCoordinates"),
            H("All affine coordinate functions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The standard constant-plus-linear equivalence for affine maps and the finite dimensional Riesz equivalence identify all affine real functions on the coordinate space with a real constant and a coordinate vector."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("native-laws"), DeclarationHandle.Create(Owner + "NativeChart"),
            H("Derived native chart laws"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The data include a linear equivalence from span N(p) onto all affine functions on the actual three-ball, with its forward map proved equal to original restriction. They include an original linear H:V->R^3 satisfying H(a(w))=w for all w, every coordinate functional of H in span N(p), and H(p)=0. For g=u-e they include g in N(p), g(a(w))=1, strict positivity of g on all K except p, and a finite positive M with norm(H(x))<=M*g(x) on the whole original cone. They also identify original comparison zero with the entire exclusion on K, prove source salience from the strict unit, prove u(Bw)=0 for all w, and give dim(span N(p))=4."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("regular-anchor-native"), DeclarationHandle.Create(Owner + "regular_anchor_native"),
            H("Original regular-anchor restriction and uniform bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Assume the original closed cone, strict unit, generation, full EB3, injective exclusion labels, an original pure p, its common confirmer e, actual regularity at p, and any full chart a of D(p). Then NativeChart data exist with exactly these original parameters. No restriction isomorphism, extension, positivity bound, support representation or shadow geometry is an input.")),
                Paragraph(Text("The existing normal-body inradius theorem supplies actual positive annihilator slopes in a whole neighborhood of zero. A positive annihilator with zero slope is constant on D(p); its global maximum is attained there. OriginalWidthContact.normalized_effect makes this scalar normalization a proper effect; its complement is an element of the full family A(p). Regularity therefore makes the annihilator a scalar multiple of g. For two positive annihilators with identical constant and slope, add the same actual opposite-slope annihilator. The sums have zero slope and coincide, so the original functionals coincide. The existing positive-span difference theorem extends injectivity to the signed normal span. The inradius and g supply every constant and slope, giving surjectivity onto all affine functions.")),
                Paragraph(Text("Pull back the three unit coordinate slopes to obtain H. Positive annihilators with slopes plus and minus r times each coordinate vector equal g plus and minus r times the corresponding coordinate functional of H. Whole-cone positivity gives absolute value of each H coordinate at most g/r; the Euclidean triangle inequality gives the finite bound M=3/r. Thus the bound includes every mixed original state and extends homogeneously to all cone vectors. For strict positivity of g on K except p, OriginalWidthContact.top_subsingleton_of_zero_exclusion applies to the same common effect e and proves that its entire maximum face is the singleton p.")),
                Paragraph(Text("ExclusionWidthCompactness.comparison_zero_iff identifies comparison(p,x)=0 with an actual original confirmer vanishing at x on the entire base, exactly the native exclusion definition. The construction establishes the original-domain input for normalized shadow ratios; width, directional support minima and boundary-distance conclusions require their additional arguments. These are consequences within the specified mathematical model; no physical realization or literature priority is asserted."))), DescribeRole.Theorem))));
}
