using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class NegativeSuffixCountExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A computed Bad count below the actual negative LARGE count constructs the complete physical source exchange without returning any SMALL.",
        H("A full exchange retaining every old SMALL"),
        Blocks(
            Describe.Lean(DescribeId.Create("negative-suffix-count-exchange-full"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NegativeSuffixCountExchange.actualSource_negativeSuffix_count_exchange_full"),
                H("A full exchange retaining every old SMALL"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The labels are Fin k for k>=3, with arbitrary natural t and the actual centered doubling source. Its cyclic permutation rho fixes n=hit(1,p) and x=hit(2,p), including the seam. Assume s(p)>0, Q<=abs(s(n)), N<3abs(s(p)), and whole-word Legal W=A++[x]++Btail. Both p and n are unused in ALL W. Every LARGE in Btail is negative. The old endpoint h satisfies C-s(p)<h<abs(s(n)). Choose an actual j in the negative LARGE filter Neg of Btail. This makes Neg nonempty; there is no lower bound such as three on its size.")),
                    Paragraph(Text("Let T be the complete actual SMALL filter, Z=Neg.erase(j), Lmax=negativeMax(s,Z), c=C-Lmax, Bad=[i in T:c<s(i)], Good=[i in T:0<s(i)<=c], and Nonpos=[i in T:s(i)<=0]. The sole new resource test is the computed strict inequality length(Bad)<length(Neg). Set F=Bad.take(1) and K=Bad.drop(1)++Good++Nonpos++Z. All SMALL remain. The theorem exposes L.Perm(K), (F++L++[j]).Perm(Btail), length(F)<=1, F contained in physical Bad, and every Bad in F++L.")),
                    Paragraph(Text("Native source geometry gives s(p)=P, s(n)=-D, s(x)=r with Q<=D<P<r<=C, D=N-2P, r=2P-D and 2P<=C+Q. Original x legality supplies b=sum(A)+P-D in [0,C-P] with C-P<=Q-1. Thus [p,n] and the optional single positive SMALL F fit without changing A. The exact raw endpoint e0=h-s(j)-P satisfies 0<e0<C from the old blocking and native budget; b+sum(F)+sum(K)=e0.")),
                    Paragraph(Text("Every unmarked positive in K is Good. Against a retained negative LARGE its compatibility follows from Good<=C-Lmax. Against a negative SMALL use the independent width 2Q-2<C; negative SMALL are never bounded by Lmax. The marked predicate is EXACTLY membership in actual Bad.drop(1). Physical filter partitions give countP(E)=length(Bad.drop(1)) and countP(s<=-Q)=length(Z)=length(Neg)-1. The strict count test supplies one extra negative LARGE whenever E is nonempty. CountSurplusOrdering.exists_order_between is used on the live proof path to construct L between b+sum(F) and e0. For one negative LARGE, Z is empty and Bad is empty; for two, no exception remains after F. No separate first-crossing or SMALL return is used.")),
                    Paragraph(Text("The literal competitor is V=A++[p,n]++F++L, with insertion [p,n] and return [x,j] ONLY. Exact physical partitions give (V++[x,j]).Perm(W++[p,n]). Reusing inventory_of_perm supplies Nodup, the full used and unused complements and all Inventory balances. The theorem proves Legal(V), InStrip from the ORIGINAL zero, and both bounds for EVERY natural take. Exactly G(V)=G(W), U(V)=U(W), H(V)+3^abs(s(x))+3^abs(s(j))=H(W)+3^abs(s(p))+3^abs(s(n)). Native energy gives strict H and J descent. The endpoint is exactly e0 in (0,C), the full unused source has mass -e0, and remainingSmall(t,V)=remainingSmall(t,W). Distinct physical labels are never identified merely because values agree.")),
                    Paragraph(Text("This arbitrary-size negative-tail theorem is conditional on the computed Bad count. It advances the actual full exchange, rather than a scalar or complement-count substitute. It does not prove universal favorable-path, representative, omitted-label or adequate-resource availability under genuine minimality, and it does not prove full C3.1. The separate native three-negative crossing-anchor route is outside this theorem. The retained declarations are symbolic mathematical content, with utility none and no finite certified-instance companion. No literature novelty is claimed."))),
                DescribeRole.Theorem)), []));
}
