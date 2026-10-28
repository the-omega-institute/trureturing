using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class InteriorNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive positive integer columns constrain both signs of every legal transition.",
        H("Integer rigidity of positive lattice transitions"),
        Blocks(
            Paragraph(Text("Matrices act on columns by left multiplication. A finite Boolean word has false=M=[[0,1],[1,1]] and true=J=[[0,1],[1,0]], and its head acts first. LegalMatrixMonoid identifies exactly its matrices with nonnegative integral matrices of determinant +1 or -1, including empty and nonempty words with identity matrix. An integer matrix A is compared with its entrywise real cast real(A).")),
            Paragraph(Text("Let v=(x,y) and r=(d,c) be strictly positive primitive integer columns, with t=xc-yd>0. A transition of integer size j>=1 sends v to vprime=(x+jd,y+jc). The determinant sign is epsilon=det(A). All inequalities below retain this same matrix and these same columns.")),
            Describe.Lean(DescribeId.Create("interiornormalform-transition-certificate"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/InteriorNormalForm.transition_certificate"),
                H("The integral transition coefficient and both rational bounds"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every nonnegative integral A of either unimodular sign satisfying Av=vprime, an integer lambda>=1 satisfies Ar=epsilon*r+lambda*vprime. The lower-left and upper-left identities are t*A10=c*(y+jc-epsilon*y)-lambda*y*(y+jc) and t*A00=c*(x+jd)-epsilon*d*y-lambda*y*(x+jd). If epsilon=1, lambda<=j*c^2/(y*(y+jc)) and y<c. If epsilon=-1, lambda<=c*(1/y+1/(y+jc)). For both signs y<2c. The displayed Lean statement includes every positivity, primitivity and action hypothesis.")),
                    Paragraph(Text("The given forward word preserves primitivity, so Bezout coefficients of vprime recover an integer multiplier from the integer vector Ar-epsilon*r parallel to vprime. In the negative-determinant branch positivity gives lambda>0. In the positive-determinant branch the strict increase of the coordinate sum on v excludes both identity and J; the same word must strictly increase the sum on the positive column r. Nonnegativity of the lower-left entry then gives both rational bounds and their consequences.")))),
            Describe.Lean(DescribeId.Create("interiornormalform-last-transition-rigidity"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/InteriorNormalForm.last_transition_rigidity"),
                H("Two consecutive increments force the last matrix"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two consecutive legal matrices K,H, suppose Kv=v+jr and H(v+jr)=v+(j+h)r, with j,h>=1 and x>d. Then j=1, y=d, c=x+hd and H=[[0,1],[1,h]]. Both initial determinant signs remain allowed.")),
                    Paragraph(Text("Apply the transition coefficient result to H with the input column v+jr. Its second coordinate is greater than c, so H has negative determinant and that coordinate is less than 2c, forcing j=1. The lower-left inequality excludes lambda>=2. The upper-left identity and x>d put the integral entry H00 between zero and one, so H00=0. Determinant -1 makes both off-diagonal entries one. The two original action equations then force y=d, c=x+hd and H11=h.")))))));
}
