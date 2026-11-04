using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldMiddleLaurentFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("FourFieldMiddleLaurentFiber", H("FourFieldMiddleLaurentFiber"), Blocks(
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-middleinput"), DeclarationHandle.Create(Prefix + "middleInput"),
                H("Seven-index numerator input"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural R,J,L,H,M,T,S, write B=b+k,Y=y+a3,Z=z+a1+a2+2k+R+J+L. The numerator input is [x+a0+3k+H+M+T+S,B-R-L-H,Z-M-T,Y-J-S]. Its total is x+b+z+y+sum(a)+6k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-middleweight"), DeclarationHandle.Create(Prefix + "middleWeight"),
                H("Exact complex binomial scalar"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight is binom(-k,R) binom(-a1,L) (-1)^J binom(-(2k+R),J) times (-1)^(H+M+T+S) binom(-k,H+M) choose(H+M,H) binom(-k,T) binom(-k,S), using the integerBinomial normalization in complex scalars."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-middlefiber"), DeclarationHandle.Create(Prefix + "middleFiber"),
                H("Exact finite admissible fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fiber contains exactly the seven natural indices for which all four signed numerator input coordinates are nonnegative. Its finite natural bounds are derived from those coordinates, including all negative target branches."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-middle-bounds"), DeclarationHandle.Create(Prefix + "middle_bounds"),
                H("Bounds forced by admissibility"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Admissibility forces R+L+H at most B, J+S at most Y and M+T at most Z, together with all cumulative native bounds and the total-degree bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-mem-middlefiber-iff"), DeclarationHandle.Create(Prefix + "mem_middleFiber_iff"),
                H("Exact membership"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership is equivalent to nonnegativity of all four original numerator inputs. No independent cutoff or finite-numerator premise is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourfieldmiddlelaurentfiber-middlecoefficient"), DeclarationHandle.Create(Prefix + "middleCoefficient"),
                H("Finite same-numerator readout"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient is the finite sum over this exact fiber of the stated scalar times the signed numerator coefficient."))), DescribeRole.Definition))));
}
