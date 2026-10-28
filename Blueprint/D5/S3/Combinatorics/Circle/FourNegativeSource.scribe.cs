using StrataLint.Scribe.Dsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class FourNegativeSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/FourNegativeSource.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive source flux excludes four negative LARGE physical labels at an original Circle minimum.",
        H("Physical positive supply and the four-negative obstruction"),
        Blocks(
            Paragraph(Text("All sets below contain physical labels. Equal source values, zero values, and shorter numerical periods are allowed. No transitivity or numerical injectivity is assumed in the finite-permutation theorem.")),
            Describe.Lean(DescribeId.Create("circle-four-negative-flux"),
                DeclarationHandle.Create(Prefix + "permutation_doubleStep_positive_flux"),
                H("Positive-part flux for a finite permutation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let rho permute a finite type, let q>0 be an integer, and let f lie between -(2q-1) and 2q-1. Assume f(rho i)=doubleStep(4q-1,f(i)) at every label. Write SP={i:0<f(i)<q}, PL={i:q<=f(i)}, and NL={i:f(i)<=-q}. Then PL and NL have the same cardinality, and sum(SP,f)+sum(NL,f after rho)=sum(PL,f). Indeed the positive labels split both as SP disjoint-union PL and as rho(SP) disjoint-union rho(NL). Cardinalities give the first identity. On SP the successor value is 2f(i); summing the second partition and cancelling one SP sum gives the flux identity. Zero contributes to neither partition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-four-negative-minimum"),
                DeclarationHandle.Create(Prefix + "actualSource_minimum_negativeLargeCount_ge_five"),
                H("An original minimum needs at least five negative LARGE labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use the native centered source f=s(k,t), k>=3, N=4Q-1 and C=2Q-1. Put n=hit(k,1,p), x=hit(k,2,p), and W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E. The literal prefix A is arbitrary and signed. Assume f(p)>0, Q<=abs(f(n)), N<3f(p), W is Legal at every natural prefix length, p and n are unused in W, every label in T0++T1++T2++E is SMALL, Q<=-f(zpen), Q<=-f(z), and f(p)<-f(y). Assume J(W)<=J(V) for every Legal physical list V of any length. The conclusion is 5<=actualNegativeLargeCount(k,t), counting all Fin(k) labels.")),
                    Paragraph(Text("Native geometry gives Q<=D<P<f(x), where P=f(p), D=-f(n)=N-2P, and D=2(C-P)+1. Nodup and unusedness make n,y,zpen,z four distinct negative LARGE labels. If there were at most four, these would exhaust NL. Suppose neither tail child rho(zpen),rho(z) is positive SMALL. Both are positive LARGE, as is rho(n)=x. These are three distinct physical positive LARGE labels; count balance leaves exactly one further PL label u. Cancelling these three contributions in the flux identity gives sum(SP,f)=f(u)-f(rho(y))<=C-(N+2f(y))<=-f(y)-1. No freshness or numerical uniqueness is required for u.")),
                    Paragraph(Text("The old legal word demands more supply. Let v be the arrival after y and a2 the arrival after z. Its departure before y gives v-f(y)<=C, and a2>=0. Telescoping the literal word gives mass(T1++T2)=-f(zpen)-f(z)+a2-v>=-f(y)+1. This SMALL segment is physically Nodup. Discarding its nonpositive entries only increases its mass, and its positive labels form a subset of SP, so its mass is at most sum(SP,f). The two bounds contradict each other.")),
                    Paragraph(Text("Thus at least one original tail gate u has 0<f(rho(u))<Q. The native negative LARGE step gives 3Q<=-2f(u). Its original departure is at most C and its arrival a is nonnegative, whence 2a<=Q-2. Since 2(C-P)>=Q-1, a<C-P. Apply FirstNegativeShiftExchange.actualSource_prefix_pair_truncation at that literal old prefix, inserting the fresh pair [p,n]. Cutting after zpen returns T2++[z]++E, which has one LARGE label; cutting after z returns E, which has none. The existing inventory gives respectively G(V)+1=G(W) or G(V)+2=G(W), hence strict J descent, contradicting the all-length minimum. This is a source-supply obstruction followed by an existing physical exchange, with no new selector or reordering of A.")),
                    Paragraph(Text("This is a repository mathematical result assembled from finite permutation counting, centered doubling and the existing exact physical inventory. No claim of literature novelty is made. Configurations with at least five negative LARGE labels and the full arbitrary signed-A Circle C3.1 problem remain open."))),
                DescribeRole.Theorem)), []));
}
