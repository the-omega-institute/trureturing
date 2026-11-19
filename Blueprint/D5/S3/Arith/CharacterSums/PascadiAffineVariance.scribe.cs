using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiAffineVarianceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/CharacterSums/PascadiAffineVariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted affine-line coverage with restricted directions, and its normalized Pascadi word instance.",
        H("Direction restrictions in the physical incidence variance"),
        Blocks(
            Describe.Lean(DescribeId.Create("direction-restricted-affine-variance"),
                DeclarationHandle.Create(Module + "direction_restricted_variance"),
                H("The centered coverage bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let p be prime. A direction is (u1,u2,1), and its line with intercept b is (b1,b2,0) plus the scalar multiples of that direction. Give every such line an arbitrary complex coefficient. Coverage at (x1,x2,t) is the sum of the coefficients with intercept (x1-t*u1,x2-t*u2). The mean is the actual average over all p cubed points.")),
                    Paragraph(Text("Assume every nonzero linear equation a*u1+b*u2+d=0 contains at most k of the selected directions. The sum of squared absolute centered coverage is at most k*p times the sum of squared absolute line coefficients. Two-dimensional Fourier orthogonality in the intercepts and one-dimensional orthogonality in t reduce the estimate to Cauchy-Schwarz in the direction fibers. The zero intercept frequency disappears by centering."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-hyperbola-affine-variance"),
                DeclarationHandle.Create(Module + "pascadi_affine_variance"),
                H("The normalized Pascadi word gives two directions per plane"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take the actual normalized word u1+u2+1=D*u1*u2 over the residue field, with D nonzero and D different from minus one. Keep nonzero coordinates and all three nonzero pair sums. These are the normalized admissible Pascadi directions, with third coordinate one.")),
                    Paragraph(Text("On this curve D*u1-1 never vanishes, so u1 uniquely determines u2. Intersecting a nonzero linear equation with the word gives the quadratic D*a*u1 squared +(D*d+b-a)*u1+b-d=0. Its coefficients cannot all vanish under the hypotheses on D. Thus every annihilator plane contains at most two directions, giving the centered coverage bound 2*p for arbitrary complex line coefficients.")),
                    Paragraph(Text("For a physical residue triple x satisfying x1+x2+x3=g*s*x1*x2*x3, normalization by its nonzero third coordinate gives D=g*s*x3 squared. The affine line through beta in direction x has normalized intercept (beta1-beta3*u1,beta2-beta3*u2). Actual signed tuple weights can therefore be aggregated into the line coefficients on a fixed D family.")),
                    Paragraph(Text("This result can be applied to signed physical line weights after fixing the normalized word parameter D. It does not estimate correlations between different D, and it does not settle the original fixed-unit prime-cube first moment or the six-return conjecture."))),
                DescribeRole.Theorem))));
}
