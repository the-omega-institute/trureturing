using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeRowParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact power parameters and an attained-endpoint identity supply the three-row physical scheduler.",
        H("Arithmetic gates for the attained three-row mask"),
        Blocks(
            Paragraph(Text("For J>=2 and m>=1, put L=J+m(J+1), r=2^J, q=2^L and k0=3L+J+4. The definitions give H=2r-1, Q=4rq^3, C=8rq^3-1 and N=16rq^3-1. modulus_identity identifies N with the original modulus 2^k0-1. parameter_bounds gives r>=4, q>=2r^2 and the exact evenness identities 2(r/2)=r and 2(q/2)=q.")),
            Paragraph(Text("The first coefficient is the natural number n=2^J times the sum of (2^(J+1))^h for 0<=h<m. coefficient_identity proves H*n=q-r, and parameter_bounds gives r<=n<q. Thus the coefficient used for physical binary selection is integral by construction; no divisibility assumption or extra occurrence is introduced.")),
            Paragraph(Text("The signed row data M,a,b,delta,e2,z1,z2,D,V1,V2,W1,W2 are the literal polynomial definitions in this module. polynomial_gates supplies the inequalities consumed by the scheduler. These are symbolic bounds over all r>=4 and q>=2r^2, rather than a finite enumeration of source instances.")),
            Paragraph(Text("bridge_arithmetic starts from H*n=q-r and the two evenness identities. Put c=(n+1)(2q+1), R=a-c-2(r-1)delta, F=R+V1-W1 and fgate=F-W2+(r/2)b-(q/2-1)z2. It proves 0<R<=C-V1, 0<F<=C, 0<fgate<C-V2 and W2+fgate<C. The exact expression for 2H*fgate is the gate polynomial, whose bounds make these attained heights available to the next physical mask.")),
            Paragraph(Text("These arithmetic identities supply the attained heights in ThreeRowScheduler and the exact actualSource correspondence in ThreeRowSource. The group-action interpretation, physical repetition and arbitrary cyclic shift belong to ThreeRowSource.exists_order. The construction concerns the explicit family above; universal j0 and the full circle conjecture remain open."))
        )));
}
