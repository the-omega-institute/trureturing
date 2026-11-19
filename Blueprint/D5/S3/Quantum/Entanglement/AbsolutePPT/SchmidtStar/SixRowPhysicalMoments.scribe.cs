using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;

internal sealed class SixRowPhysicalMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical boundary moments from an ordered six-row APPT spectrum", H("SixRowPhysicalMoments"), Blocks(
            Describe.Lean(DescribeId.Create("sixrowphysicalmoments-constraints"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalMoments.Constraints"),
                H("Normalized physical moment constraints"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The predicate retains the actual lists h on Fin 15 and d on Fin 21. Write H and D for their sums, a and q for their sums of squares, and s=6-15*r-H-D. It requires 0<=r<=2/5, nonnegative heads, nondecreasing tails in [0,1], the zero slots h[14]=d[0]=0, nonnegative sums and energies, and s>=0. The finite moment bounds are H^2<=14*a, D^2<=20*q, a<=H^2, q<=D and q<=D^2.")),
                    Paragraph(Text("With c=(4-8*r-5*r^2)/(2-3*r), the predicate requires h[i]<=c, a<=c*H and the separate bound a<=(H-c)^2+c^2. It also requires q<=max(2,2*D/3) and (5/7)*(a-H^2/15)+(q-D^2/21)<=4*s-s^2/3. The Cauchy factors 14 and 20 omit the respective zero slots; the variance centers use all 15 and 21 slots."))
                ), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowphysicalmoments-literal-moments"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalMoments.literal_moments"),
                H("Literal APPT supplies the boundary moments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n>=23 and N=6*n, take an antitone nonnegative spectrum l on Fin N of sum one, with APPT of its complex diagonal in the supplied product labelling e : (Fin 6 × Fin n) ≃ Fin N. With zero-based indices set U=l[N-21], B=l[14], V=B-U, r=V/U, h[i]=(l[i]-B)/U for the first fifteen slots and d[j]=(U-l[N-21+j])/U for the last twenty-one. The theorem gives U>0 and Constraints r h d for these very lists. Ordering and nonnegativity give their signs, the tail ordering and unit bound, and the exact zero slots. Removing those slots gives the two Cauchy bounds.")),
                    Paragraph(Text("The literal rank-six head cap supplies U>0, 0<=15*V<=6*U and 8*V^2<=(3*U-L)*(2*U-3*V) for L=l[0]. Divide by U^2 and use 2-3*r>0 to obtain h[0]<=c, then use ordering for all heads. Summing h[i]^2<=c*h[i] gives the linear bound. For the separate quadratic bound, use the common cap c if H>=2*c, or H-c if every head is at most H-c. In the remaining case erase a slot j with h[j]>H-c; the other squares sum to at most (H-h[j])^2, and the gap from the desired bound is 2*(c-h[j])*(c+h[j]-H)>=0.")),
                    Paragraph(Text("Literal APPT gives a PSD matrix for independently bijective labels of both pools. The all-ones quadratic form equals 2*S, where S is the bottom pool sum minus the top pool sum, hence S=U*s>=0. For the tail estimate, put deficit labels 20 and 19 on diagonal slots 0 and 1 and label 18 on their edge, using all other labels once. The PSD entry-square inequality, valid also for a singular matrix, gives d[18]^2<=4*(1-d[20])*(1-d[19]) after discarding a nonnegative head and gap contribution from the off-diagonal magnitude.")),
                    Paragraph(Text("Write x=d[20], y=d[19], z=d[18] and t=x+y. The minor and ordering give 2*z<=t<=2-z, so z<=2/3. All entries except x and y are at most z. The minor and (t-2*z)*(t-2+z)<=0 bound x^2+y^2-z*t by 2-4*z+3*z^2/2. Thus q<=z*D+2-4*z+3*z^2/2. For m=max(D,3), the gap between 2*m/3 and this last bound with D replaced by m is (2/3-z)*(m-3+3*z/2)>=0. This gives the stated tail cap on the entire list.")),
                    Paragraph(Text("The rank-six literal variance moment bounds (5/7) times the centered top energy plus the centered bottom energy by 4*S*min(bottom pool sum/7,U)-S^2/3. Since S>=0, replacing the minimum by U gives 4*U*S-S^2/3. The centered energies are U^2*(a-H^2/15) and U^2*(q-D^2/21), because the pool values are U*(1+r+h[i]) and U*(1-d[j]). Dividing by U^2 and using S=U*s yields exactly 4*s-s^2/3 on the right. The same-vector coupling is a separate supplier."))
                ), DescribeRole.Theorem)
        )));
}
