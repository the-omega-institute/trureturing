using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyAsymmetricGrowthDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full odd asymmetric lattice quotients have exact finite order, ball growth and signed Cayley diameter.",
        H("Exact growth and diameter of asymmetric lattice quotients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-full-asymmetric-quotient-growth"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyAsymmetricGrowth.asymmetric_quotient_growth"),
                H("The full odd asymmetric lattice family has exact growth and diameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let p,m,a,b be odd integers with p≥3 and 0<a,b<m. In Z² put v₁=(p(m−a)/2,p(m+a)/2), v₂=(p(m−b)/2,−p(m+b)/2), K=Zv₁+Zv₂ and G=Z²/K. The halves are integral. Let F be the canonical quotient map, let f(x,y)=F(x,y) under the standard identification with integer pairs, and put s=(pm−1)/2. Then G is finite and noncyclic, with |G|=p²(m²−ab)/2. For every natural r≤s, put wₐ=2r−p(m−a)+1 and wᵦ=2r−p(m−b)+1. The exact identity is |f(Dᵣ)|+⌊(max(0,wₐ)max(0,wᵦ)+1)/2⌋=2r²+2r+1. The positive parts are taken in the integers before conversion to natural numbers.")),
                    Paragraph(Text(
                        "The same quotient map F covers at radius s and fails to cover at radius s−1. More precisely, for every natural R, LeeCovers(F,R) holds exactly when s≤R. Thus s is the signed Cayley diameter for the coordinate images F(1,0),F(0,1). All conclusions refer to this actual quotient and this same pair. No primality assumption on p is used, and no condition comparing 2min(a,b) with m is needed.")),
                    Paragraph(Text(
                        "The map S(x,y)=(x+y,x−y) sends v₁ to (pm,−pa) and v₂ to (−pb,pm). Hence the Lee norm of q₁v₁+q₂v₂ is p max(|mq₁−bq₂|,|−aq₁+mq₂|). If q₁,q₂ are nonnegative and unequal, the larger coefficient exceeds the smaller by at least one; the corresponding coordinate has absolute value at least m, because m−a and m−b are positive. Simultaneous negation handles two nonpositive coefficients. For opposite signs the terms add in absolute value, and a nonzero integer coefficient supplies the same lower bound. Unequal coefficients therefore cost at least pm in Lee norm.")),
                    Paragraph(Text(
                        "For r≤s, a relation of norm at most 2r has norm at most pm−1. Its coefficients must coincide, so it is an arbitrary integer multiple of h=v₁+v₂. The vector h is nonzero and lies in K; S(h)=(p(m−b),p(m−a)). The imported BajnokBeattyExtremalGrowth.lee_ball_image_card_of_displacement applies directly. Its two rectangle widths are precisely the positive parts of wᵦ and wₐ. This argument includes fibers of arbitrary finite length; it does not reduce the relations to 0,h,−h.")),
                    Paragraph(Text(
                        "The determinant is −p²(m²−ab)/2 and is nonzero since ab<m². The existing two-vector index theorem identifies its absolute value with |G|, giving finiteness. Every coordinate of v₁ and v₂ is divisible by p, so reduction modulo p induces a surjection G→(Z/pZ)². A product of two cyclic groups of order p is cyclic only when their orders are coprime. Since p≥3, this quotient is noncyclic, and G is noncyclic as well. This uses the modulus p itself, including composite p.")),
                    Paragraph(Text(
                        "At r=s the widths are pa,pb, both positive and odd. Substituting their half-product cap count into the growth identity gives |f(Dₛ)|=|G|, hence actual coverage. At r=s−1 the widths are pa−2,pb−2, again positive and odd. The same count gives the exact deficit |G|−|f(Dₛ₋₁)|=p(2m−a−b)>0. This proves failure of coverage one step below s; monotonicity of the Lee bound then proves the covering equivalence for every natural R. The growth formula is asserted only through s, whereas the covering equivalence has no upper radius restriction.")),
                    Paragraph(Text(
                        "For p=3,m=11,a=b=9, the basis is (3,30),(3,−30), the group has order 180 and the diameter is 16. At radius 15 both widths equal 25, so the cap has 313 points and the image has 481−313=168 points. Here 2min(a,b)=18>11, and h=(6,0) permits long fibers. This instance illustrates why the full rank-one fiber statement is needed.")),
                    Paragraph(Text(
                        "Bajnok–Beatty, https://arxiv.org/abs/2406.04045v1, provides the Cayley-diameter context and known lower constructions. The asymmetric quotient family, its coefficient-separation argument and its deduction of exact diameter from the full growth identity are repository derivations from the finite-fiber and determinant-index results. They are not attributed to that paper, and no novelty or open-problem claim is made."))),
                DescribeRole.Theorem))));
}
