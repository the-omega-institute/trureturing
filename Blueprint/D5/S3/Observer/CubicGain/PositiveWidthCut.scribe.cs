using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class PositiveWidthCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive fifth readings force strict width below the positive cubic root",
        H("Positive parent width cut"),
        Blocks(
        Paragraph(Text("There is a unique positive real β satisfying β³−8β−4=0. Every strict parent C=(r,b,ε), with 0<r<1, b>0 and εΛ+(24/5)(b−1/8)(6/(1+b)−2/(1+2b))=0, whose literal fifth response is positive satisfies b<β. Every original complete world with positive clock-five reading satisfies the same strict width bound.")),
        Paragraph(Text("The intermediate value theorem gives a root in (3,31/10). A positive root must exceed two: for 0<x≤2, x³≤4x<8x+4. For 2≤x<y, the difference of the cubic values is (y−x)(y²+xy+x²−8)>0. This proves uniqueness among all positive real roots.")),
        Paragraph(Text("Write j=b+r(1−r)/b, n=j+r, T=1+b, U=1+2b, X=b²+r(1−r), N=X+br, k=fifthDrift(r,b), and F=parentEq(r,b,ε). Direct denominator clearing gives pΛ−kF=−6Q(r,b)/(5bTUXN). For t=b−3, the polynomial Q=Σᵢ₌₀⁷qᵢ(r)tⁱ has the following coefficients.")),
        Paragraph(Text("q₀=736r⁶−6624r⁵−11616r⁴+149321r³−63651r²−508239r+824823; q₁=256r⁶−3776r⁵−14856r⁴+181595r³−31780r²−1023870r+1657449.")),
        Paragraph(Text("q₂=−512r⁵−5904r⁴+82287r³+22306r²−849479r+1406376; q₃=−744r⁴+16429r³+20156r²−372027r+650370.")),
        Paragraph(Text("q₄=1216r³+5217r²−90786r+175855; q₅=456r²−11711r+27501; q₆=2258−624r; q₇=72.")),
        Paragraph(Text("On 0≤r≤1, bound every negative monomial −arʲ below by −a and every positive nonconstant monomial below by zero. In increasing degree this gives qᵢ≥[234693,583167,550481,277599,85069,15790,1634,72]. Equivalently, each coefficient is its listed positive lower bound plus nonnegative multiples of rʲ and 1−rʲ. Hence Q>0 for all b≥3.")),
        Paragraph(Text("If b≥β, monotonicity of the cubic above two gives b³−8b−4≥0. The identity 1+6/T+1/U−8/b=2(b³−8b−4)/(bTU), together with j>b and n>b for strict r, gives Λ>0. In an actual parent F=0, so the identity for pΛ has negative right side and positive left side when p>0, a contradiction.")),
        Paragraph(Text("The original-world coordinate correspondence supplies the strict parent and preserves the literal fifth reading and width. The polynomial gain remains one whole nonzero real polynomial of degree at most three, with one fixed drift and all five original rows. Lower degrees, sampled zeros, repeated roots, zero drift and singular parents remain included. The result concerns the strict upper bound only; it asserts no endpoint approach, sharpness, cutoff or terminal uniqueness.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-positive-parent-width-cut"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/PositiveWidthCut.positive_parent_width_cut"),
            H("Strict width bound for every positive parent"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There exists β>0 with β³−8β−4=0, and every positive real root equals β; simultaneously, every strict native parent with fifthResponse>0 has width below β, and every complete original world with originalRead W 5>0 has width below the same β."))),
            DescribeRole.Theorem))));
}
