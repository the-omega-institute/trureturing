using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class InteriorNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive positive integer columns constrain both signs of every legal transition.",
        H("Integer rigidity of positive lattice transitions"),
        Blocks(
            Paragraph(Text("Matrices act on columns by left multiplication. A finite Boolean word has false=M=[[0,1],[1,1]] and true=J=[[0,1],[1,0]], and its head acts first. LegalMatrixMonoid identifies exactly its matrices with nonnegative integral matrices of determinant +1 or -1, including empty and nonempty words with identity matrix. An integer matrix A is compared with its entrywise real cast real(A).")),
            Paragraph(Text("Let v=(x,y) and r=(d,c) be strictly positive primitive integer columns, with t=xc-yd>0. A transition of integer size j>=1 sends v to vprime=(x+jd,y+jc). The determinant sign is epsilon=det(A). All inequalities below retain this same matrix and these same columns.")),
            Paragraph(Text("For every integer matrix A and integer x,y,d,c,j, TransitionHypotheses means precisely nonnegative entries, determinant +1 or -1, x,y,d,c>0, gcd(x,y)=gcd(d,c)=1, xc-yd>0, j>=1, and A*(x,y)=(x+jd,y+jc). TransitionCertificate(A,x,y,d,c,j,l) is exactly the conjunction of the eight conclusions below, including l>=1, the vector identity, both entry identities, both determinant-conditional rational bounds, the positive-sign y<c implication and y<2c.")),
            Describe.Lean(DescribeId.Create("interiornormalform-transition-certificate"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/InteriorNormalForm.transition_certificate"),
                H("The integral transition coefficient and both rational bounds"), StatementSource.FromAuthor(Disp(Seq(Forall,Sp,F.Id("A"),Comma,F.Id("x"),Comma,F.Id("y"),Comma,F.Id("d"),Comma,F.Id("c"),Comma,F.Id("j"),Comma,Sp,C("TransitionHypotheses",F.Id("A"),F.Id("x"),F.Id("y"),F.Id("d"),F.Id("c"),F.Id("j")),Implies,Sp,Exists,Sp,F.Id("l"),InMacro,Sp,Mathbb,Grp(F.Id("Z")),Comma,Sp,C("TransitionCertificate",F.Id("A"),F.Id("x"),F.Id("y"),F.Id("d"),F.Id("c"),F.Id("j"),F.Id("l"))))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every nonnegative integral A of either unimodular sign satisfying Av=vprime, an integer lambda>=1 satisfies Ar=epsilon*r+lambda*vprime. The lower-left and upper-left identities are t*A10=c*(y+jc-epsilon*y)-lambda*y*(y+jc) and t*A00=c*(x+jd)-epsilon*d*y-lambda*y*(x+jd). If epsilon=1, lambda<=j*c^2/(y*(y+jc)) and y<c. If epsilon=-1, lambda<=c*(1/y+1/(y+jc)). For both signs y<2c. The hypotheses retain every positivity, primitivity and action condition.")),
                    Paragraph(Text("The given forward word preserves primitivity, so Bezout coefficients of vprime recover an integer multiplier from the integer vector Ar-epsilon*r parallel to vprime. In the negative-determinant branch positivity gives lambda>0. In the positive-determinant branch the strict increase of the coordinate sum on v excludes both identity and J; the same word must strictly increase the sum on the positive column r. Nonnegativity of the lower-left entry then gives both rational bounds and their consequences.")))),
            Paragraph(Text("TwoTransitionHypotheses(K,H,x,y,d,c,j,h) means exactly the positivity, primitivity, t>0, x>d, j,h>=1, nonnegative integer entries and either unimodular determinant sign for both matrices, and the two consecutive action equations stated below.")),
            Describe.Lean(DescribeId.Create("interiornormalform-last-transition-rigidity"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/InteriorNormalForm.last_transition_rigidity"),
                H("Two consecutive increments force the last matrix"), StatementSource.FromAuthor(Disp(Seq(Forall,Sp,F.Id("K"),Comma,F.Id("H"),Comma,F.Id("x"),Comma,F.Id("y"),Comma,F.Id("d"),Comma,F.Id("c"),Comma,F.Id("j"),Comma,F.Id("h"),Comma,Sp,C("TwoTransitionHypotheses",F.Id("K"),F.Id("H"),F.Id("x"),F.Id("y"),F.Id("d"),F.Id("c"),F.Id("j"),F.Id("h")),Implies,Sp,F.Id("j"),Eq,D(1),Land,Sp,F.Id("y"),Eq,F.Id("d"),Land,Sp,F.Id("c"),Eq,F.Id("x"),Plus,F.Id("h"),F.Id("d"),Land,Sp,C("H",D(0),D(0)),Eq,D(0),Land,Sp,C("H",D(0),D(1)),Eq,D(1),Land,Sp,C("H",D(1),D(0)),Eq,D(1),Land,Sp,C("H",D(1),D(1)),Eq,F.Id("h")))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two consecutive legal matrices K,H, suppose Kv=v+jr and H(v+jr)=v+(j+h)r, with j,h>=1 and x>d. Then j=1, y=d, c=x+hd and H=[[0,1],[1,h]]. Both initial determinant signs remain allowed.")),
                    Paragraph(Text("Apply the transition coefficient result to H with the input column v+jr. Its second coordinate is greater than c, so H has negative determinant and that coordinate is less than 2c, forcing j=1. The lower-left inequality excludes lambda>=2. The upper-left identity and x>d put the integral entry H00 between zero and one, so H00=0. Determinant -1 makes both off-diagonal entries one. The two original action equations then force y=d, c=x+hd and H11=h.")))))));
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var arg in args)
        {
            if (parts.Count > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(arg);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts.ToArray()), Close);
    }

}
