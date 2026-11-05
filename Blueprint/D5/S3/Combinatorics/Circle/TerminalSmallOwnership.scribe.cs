using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TerminalSmallOwnershipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal SMALL ownership and the actual two-step orbit transition for an arbitrary physical signed source word.",
        H("Terminal SMALL ownership and orbit transition"),
        Blocks(
            Paragraph(Text("For the actual centered source f=s(k,t), retain every physical Fin(k) occurrence in W=F++[z]++E. Assume k>=3, f(p)>0, Q<=|f(n)| for n=hit(k,1,p), N<3|f(p)|, Legal W, p and n absent from the whole W, every occurrence of E SMALL, Q<=-f(z), and J(W)<=J(V) for every Legal physical list V of every length. F is an arbitrary signed literal prefix. Put P=f(p), D=|f(n)|, B=C-P, d=P-D, u=mass(f,F), and q(m)=mass(f,F++[z]++E.take(m)).")),
            Describe.Lean(DescribeId.Create("terminal-small-ownership-prefix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TerminalSmallOwnership.actualSource_terminal_small_ownership_prefix"),
                H("Forced endpoint corridor and nonnegative SMALL ownership"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The consumed prefix proves C-d<u, B<q(m)<D for every natural m including saturated takes, and usedness of every physical i with |f(i)|<Q and 0<=f(i). Native geometry gives f(n)=-D, D=2B+1, d>0, d<=B and 2d<=Q-1. The low-prefix competitor is (F++[z]++E.take(m))++[p,n], returning E.drop(m); the high-prefix competitor appends [n] to that same retained prefix. Both strictly lower G because the returned suffix contains only SMALL labels. The departure competitor F++[n,p] returns exactly [z]++E and also strictly lowers G.")),
                    Paragraph(Text("For a fresh nonnegative SMALL i, a legal append W++[i] keeps G,H and decreases U by one, including f(i)=0. If that append fails, F++[z]++[i,n] is Legal and consumes one additional LARGE label. Its mixed accounting uses the Nodup-only baseline W++[i] and the existing all-LARGE inventory for [n]; no false original-W all-LARGE insertion premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("terminal-small-ownership-transition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TerminalSmallOwnership.actualSource_terminal_small_ownership_transition"),
                H("Unused negative SMALL boundaries and the genuine two-step dichotomy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The full theorem consumes the prefix on its live proof path and retains all its conclusions. For every physical i absent from W with |f(i)|<Q, put sigma=-f(i). Then 0<sigma<Q, q(m)<sigma for every natural m, and u-D<sigma. Its actual first successor j=hit(k,1,i) satisfies f(j)=-2sigma and Q<=-f(j). Either j already belongs to W, or u<2sigma and the actual second successor hit(k,2,i) belongs to W with 0<f(hit(k,2,i))<=2d-3<Q.")),
                    Paragraph(Text("Unused SMALL i is negative by nonnegative SMALL ownership. If sigma<=mass(f,W), the literal append W++[i] has legal endpoint mass(f,W)-sigma and strictly decreases U. Thus sigma exceeds the endpoint and B. If sigma<=q(m), put K=F++[z]++E.take(m) and R=E.drop(m). The literal competitor K++[i,p] returns R and has new heights q(m)-sigma and q(m)-sigma+P in [0,C]; its exact balance is G(new)+1=G(W). Consequently sigma>q(m) for all m.")),
                    Paragraph(Text("If sigma<=u-D, the literal competitor F++[n,i,p] returns exactly [z]++E. Its successive new heights are u-D, u-D-sigma and u-D-sigma+P. The lower gates follow from the supposition, and the final upper gate follows from sigma>B>=d and u<=C. Direct physical_balance with largeWeight gives G(new)+2=G(W)+1. The SMALL insertion is counted physically, without asserting an Inventory whose inserted labels are all LARGE.")),
                    Paragraph(Text("The seam-inclusive source_cycle gives the true centered-doubling law on physical rotations. Since B<sigma<Q and D=2B+1, the first value is -2sigma and is negative LARGE. If this j is fresh and 2sigma<=u, the literal competitor F++[j,p] returns [z]++E, with new heights b=u-2sigma and b+P. The inequalities sigma>u-D and C-d<u imply b<=B-2, so these gates are legal; both inserted labels are fresh LARGE and G(new)+2=G(W)+1. Therefore a fresh j forces u<2sigma.")),
                    Paragraph(Text("In that fresh-child branch, centered doubling gives the actual second value lambda=N-4sigma. Integrality and sigma<=Q-1 imply lambda>=3. From 2sigma>=u+1 and u>=C-d+1, lambda<=2d-3; the native budget 2d<=Q-1 makes lambda<Q. The already proved nonnegative SMALL ownership makes this actual physical second successor used. The argument allows the fresh-child branch to be empty for small d and does not assume a numerical source period or injectivity.")),
                    Paragraph(Text("Every retained prefix and returned suffix is literal. Freshness is against the whole original W; SMALL/LARGE or opposite signs prove distinctness only for the inserted physical labels. The shared private cut helper proves Nodup and the G balance directly from physical_balance. Mixed insertions do not preserve remainingSmall unchanged: the fresh SMALL label is removed from the unused SMALL set. No used child is treated as fresh, and no physical label is spent twice.")),
                    Paragraph(Text("For the original H1-H12 word W=A++[hit(k,2,p)]++T0++[y]++T1++[zpen]++T2++[z]++E, take F=A++[hit(k,2,p)]++T0++[y]++T1++[zpen]++T2. H8 restricts to E, H10 supplies the terminal negative LARGE, and the same H12 compares all Legal lengths. H9 and H11 remain additional original assumptions; the stronger theorem needs neither. This is a conditional specialization, with no concrete terminal-minimum instance asserted.")),
                    Paragraph(Text("The terminal ownership conclusions alone do not supply an exchange for every arbitrary signed F. For the full word with additional negative LARGE y,zpen and intervening SMALL batches, ThreeNegativeExchange.actualSource_threeNegative_exchange_full gives a strict-J Legal competitor by a positive terminal overshoot and three physical reroutings. This stronger three-negative conclusion requires no unused SMALL resource or inverse-parent premise. Used successors are never treated as fresh resources."))),
                DescribeRole.Theorem)), []));
}
