using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak with equal tails: the three-cone native union",
        H("One physical word, adaptive X allocation and a ceiling W mask"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-second-peak-equal-tail-cones-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Endpoint.actualSource_second_peak_equal_tail_cones_joint_lift"),
                H("The complete five-binder stronger union"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This source replaces the earlier region at the same canonical declaration. It has " +
                        "exactly five original binders: natural a,b,s, hs:2<=s, and hcone:((2s+2<=a and a+1<=b) or " +
                        "(s+1<=a and max(a+1,3s+1)<=b)) or (2<=a and a+1<=s and 2s+1<=b). " +
                        "Let k=a+b+s+s and A=1+2^a+2^(a+b)+2^(a+b+s). One physical " +
                        "permutation sigma:List(Fin k) and one literal cut j<=k satisfy both " +
                        "OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)). Each " +
                        "OriginalOrder retains its physical permutation, exact zero total, and every natural " +
                        "take-prefix, including empty and overlong prefixes. Status is SOURCE_ONLY_UNELABORATED; " +
                        "actual kernel, audit and official acceptance remain outstanding.")),
                    Paragraph(Text(
                        "Write x=2^a,y=2^b,z=2^s, D=y(z+1)+1 and N=xyz^2-1. The old heads are A=xD+1, " +
                        "B=xz(y+1)+z+1, L=xz^2+z^2+z+1, M=yz^2+D. The new heads are 2A, Bn=2B-1, Ln=2L-z-1, " +
                        "Mn=2M-D, for Q=2N+1. The eight recurrences are zA=N+B, zB=N+L, yL=N+M, xM=N+A, " +
                        "z(2A)=Q+Bn, zBn=Q+Ln, yLn=Q+Mn, xMn=Q+A. Pinned PacketNormalForm.Source identifies these " +
                        "with actual centered residues at the physical chain offsets 0,s,2s,2s+b and lengths " +
                        "s,s,b,a. Every nonterminal power is positive and every terminal is negative. The old " +
                        "total is zero; the new old-label total is -A and the true fresh label k has value A.")),
                    Paragraph(Text(
                        "On the old two-clause union let lambda=2^(b-a-1), epsilon=0 when b=a+1 and lambda/2 otherwise. The W mask is " +
                        "p=y/(2z)+y/z^2-1-epsilon, with capacities H=y/z-1 and F=y/2-1. The stronger native X " +
                        "allocation is C=x/(2z)-delta, delta=1 when b>=3s+1 and 0 otherwise; E=x/2-1 is its full " +
                        "capacity. Natural exponent identities prove divisibility and all cast/subtraction bounds " +
                        "before any bit allocation. Under a>=s+1, 2lambda<=y/(2z) gives p>=0; z>=4 gives p<=H. " +
                        "Also 0<=C<=E. Only H,F,E must be all-ones masks. When delta=0, C itself can be a general " +
                        "submask of E. When a=s+1 and b>=3s+1, C=0 exactly; no X label or chain is removed.")),
                    Paragraph(Text(
                        "For that old allocation the terminal order is W,U,X,V. Bank 1 contains all U positives and W mask p, then W " +
                        "terminal. Bank 2 contains all V positives, W mask H XOR p and X mask C, then U terminal. " +
                        "Bank 3 contains W mask F XOR H, then X terminal. Bank 4 contains X mask E XOR C, then V " +
                        "terminal. Increasing physical-bit decoding and exact nested-mask splits prove that every " +
                        "old physical label occurs once. The cut j is the combined length of banks 1 and 2, " +
                        "including their terminals. The fresh label k is inserted at START bank 3. All " +
                        "complements are proved equal to H-p,F-H,E-C in the integers; paired masses use the same " +
                        "physical masks in both centered rows.")),
                    Paragraph(Text(
                        "The old inventory gives the cumulative factorization 2S1=(z-2)A+2Lp-N+M, " +
                        "2T1=2(z-2)A+2Ln*p-Q+Mn, 2S2=(z-2)(A+B)+2LH+2MC-2N+M+B, " +
                        "2T2=(z-2)(2A+Bn)+2Ln*H+2Mn*C-2Q+Mn+Bn, 2S3=(2C+2)M-A-L and 2T3=(2C+2)Mn-A-Ln. These " +
                        "follow by source recurrences and literal inventory, including fresh A precisely from " +
                        "seam 3. In particular the second seam is independent of p. The late mask and early mask " +
                        "have different arithmetic jobs. Switching delta from 1 to 0 raises the third doubled " +
                        "seams by 2M and 2Mn while preserving the exact physical partition.")),
                    Paragraph(Text(
                        "The threshold five charts cover a>=2s+2: high-a adjacent and separated use a>=3s, " +
                        "u=2^(s-2), v=2^(a-3s), z=4u, x=64u^3v, and w=2^(b-a-2) in the separated case. Their " +
                        "(lambda,epsilon) are (1,0) and (2w,w). For a<3s,b>=3s+1 use " +
                        "u=2^(a-2s-2),v=2^(3s-a-1),w=2^(b-3s-1), z=8uv,x=256u^3v^2,(lambda,epsilon)=(2vw,vw). For " +
                        "b<=3s and b=a+1 use u=2^(a-2s-2),v=2^(3s-b),z=8uv,x=256u^3v^2,(lambda,epsilon)=(1,0). " +
                        "For b<=3s and b>=a+2 use " +
                        "u=2^(a-2s-2),v=2^(b-a-2),w=2^(3s-b),z=16uvw,x=1024u^3v^2w^2,(lambda,epsilon)=(2v,v). " +
                        "Delta is 1 in the first three charts and 0 in the last two.")),
                    Paragraph(Text(
                        "The three additional old-union charts cover s+1<=a<=2s+1,b>=3s+1, with y=2z^3R and delta=1. At " +
                        "a=s+1 use u=2^(s-2),v=2^(b-3s-1),z=4u,x=8u,R=v,epsilon=4u^2v,C=0. For s+2<=a<=2s use " +
                        "u=2^(a-s-2),v=2^(2s-a),w=2^(b-3s-1),z=4uv,x=16u^2v,R=w,epsilon=2uv^2w,C=2u-1. At a=2s+1 " +
                        "use u=2^(s-2),v=2^(b-3s-1),z=4u,x=32u^2,R=v,epsilon=uv,C=4u-1. Every chart variable is " +
                        "at least 1. The chart proofs derive all eleven dyadic powers and epsilon directly from " +
                        "natural gap premises, including a=s+1,b=3s+1 and s=2. No exponent is silently truncated.")),
                    Paragraph(Text(
                        "For each chart and seam r=1,2,3 the four exact gates are 2S_r, successor_r-1-2S_r, 2T_r " +
                        "and newSuccessor_r-1-2T_r. The eight chart modules supply all 96 ring/positivity proofs. " +
                        "They group all 6145 positive shifted coefficients into exact Horner expressions after " +
                        "u=1+U,v=1+V,w=1+W. Ring equates each expression with its actual defining seam gate; " +
                        "positivity uses U,V,W>=0. This avoids duplicated original expansions and imports no " +
                        "Python truth as an axiom. The old three-chart source was preserved before replacement. " +
                        "The caller reports actual ordinary Pro APPROVE receipts for these two OLD clauses; " +
                        "they do not cover the new lower-a ceiling branch. The supplied 60+36 exact identities and 633+916 " +
                        "physical controls remain ordinary diagnostics.")),
                    Paragraph(Text(
                        "The third clause is the unbounded region 2<=a<s, b>=2s+1. Here x>=4, z>=2x, y>=2z^2. " +
                        "The natural differences u=2^a-4, v=2^s-2*2^a and w=2^b-2*2^s*2^s are nonnegative; " +
                        "safe cast identities give x=4+u, z=2x+v, y=2z^2+w, including w=0 on b=2s+1. LowerPolynomial supplies all 13 new " +
                        "exact ring/positivity proofs containing the complete 373 positive coefficient literals. " +
                        "The coefficient file supplies expressions; neither its diagnostics nor Python truth " +
                        "is imported as an axiom. Every new helper feeds the same sole public endpoint.")),
                    Paragraph(Text(
                        "In this branch C=ceil((M-L)/(2L)) is the actual natural quotient " +
                        "(M-L+2L-1).toNat/(2L).toNat. LowerCeiling first proves M-L>=1 and L>=1, making both " +
                        "conversions safe. Natural quotient-remainder arithmetic proves M-L<=2LC<=M+L-1. " +
                        "The positive capacity polynomial L(y-3)-M+1 proves C<=F=y/2-1. Only F must be " +
                        "all-ones; C may have arbitrary bits. Its native complement F XOR C=F-C gives disjoint " +
                        "physical subsets whose union is all W positives. No a>=s+1 or old adaptive X mask " +
                        "is imposed in this branch.")),
                    Paragraph(Text(
                        "The lower branch keeps terminal order W,U,X,V. Bank 1 is all U positives/W terminal; " +
                        "bank 2 is all X positives, W mask C/U terminal; bank 3 is all V positives/X terminal; " +
                        "bank 4 is W mask F XOR C/V terminal. The complementary W mask occurs in BANK 4 only. " +
                        "LowerPhysical proves the complete old occurrence inventory and both exact bank masses. " +
                        "The true fresh k starts bank 3, after the first two terminals. The literal cut is " +
                        "lowerPre.length, bounded by k using the inventory, and the inherited labels are the " +
                        "same Fin.castSucc physical occurrences in the second word.")),
                    Paragraph(Text(
                        "For clarity use D_i,E_i for doubled cumulative POSTTERMINAL prefixes. The local old " +
                        "bank increments are d1=B+M-2A, d2=A+B-2M+2CL, d3=L-2B+A; the new increments are " +
                        "e1=Bn+Mn-4A, e2=A+Bn-2Mn+2CLn, e3=Ln-2Bn+3A. LowerSeams explicitly proves these " +
                        "individual increments from source recurrences, then sums them: D2=d1+d2=2B-A-M+2CL, " +
                        "D3=d1+d2+d3=(2C+1)L-M; E2=e1+e2=2Bn-3A-Mn+2CLn, " +
                        "E3=e1+e2+e3=(2C+1)Ln-Mn. Thus none of the displayed cumulative seams is being " +
                        "mistaken for an individual bank increment. The fresh doubled 2A is included in e3.")),
                    Paragraph(Text(
                        "The 13 positive polynomials are B+M-2A, 2A-B-1, Bn+Mn-4A, 4A-Bn-1, " +
                        "2B-A-L, A-B-L, L(2Bn-3A-Ln)+Az^2, L(3A-Bn-1-Ln)-Az^2, A-2L, Az^2, " +
                        "L(A-1-2Ln)-Az^2, M-L, L(y-3)-M+1. LowerSeams proves Delta=M*Ln-Mn*L=Az^2. " +
                        "Rounding and Delta give all 12 cumulative gates with caps (M-1,Mn-1), (B-1,Bn-1), " +
                        "(A-1,A-1), and both fourth seams are exactly zero. The residual M-2CL may be negative: " +
                        "the true old requirement is L-A+1<=M-2CL<=L, rather than the unnecessary positive " +
                        "residual restriction. Removing that extra restriction does not weaken OriginalOrder. " +
                        "LowerSchedule consumes the gates through Checks, checks_strip and lift_order for " +
                        "both full actual source orders and all natural prefixes, including the fresh prefix.")),
                    Paragraph(Text(
                        "Complete ordinary Pro reviews approve the threshold cone, its old-union extension, " +
                        "and the lower-a construction for every 2<=a<s and b>=2s+1, including the boundary w=0. " +
                        "These mathematical reviews do not certify Lean elaboration, kernel checking or official " +
                        "acceptance. The independent complete integer identity check has degree caps (7,5,1) " +
                        "and difference coefficient l1 bound 82850052<2^128; all 13 constants are positive. " +
                        "The supplied 2246 complete physical/full-prefix controls, including b=1000, are " +
                        "ordinary diagnostics.")),
                    Paragraph(Text(
                        "The fourth seams vanish by the eight recurrences and total native capacities. Within " +
                        "each bank, both source rows have nonnegative increments, with the fresh new increment A " +
                        "positive at bank 3. If a terminal has old successor R, its doubled magnitude is N-R and " +
                        "its post-terminal seam is at most (R-1)/2; thus the preceding bank peak is at most " +
                        "(N-1)/2. The analogous new bound is (Q-1)/2=N. The pinned checks_strip and lift_order " +
                        "proofs consume these gates for every natural prefix; exact zero totals also cover takes " +
                        "beyond the complete word. The final literal marked_word transport identifies the second " +
                        "physical word with earWord at the very same j.")),
                    Paragraph(Text(
                        "The owning Reg uses type_of% of this exact five-binder declaration, the full dependent " +
                        "whole-family law, coordinates [0,1,2] and both actual OriginalOrder function readouts. " +
                        "It proves rejected-family variation, deletion sensitivity for each role, and actual " +
                        "observational dependence on a valid parameter fiber. Literal sourceSelection paths " +
                        "traverse the full theorem body. FamilyRecord is none and continuation is unknown. " +
                        "Compilation and current source reconstruction must validate this registration; a proxy " +
                        "proposition or a specialized parameter fiber does not supply the family theorem.")),
                    Paragraph(Text(
                        "Multiplication by 2 acts on residues modulo 2^k-1 and 2^(k+1)-1; the actual centered " +
                        "sections produce these arithmetic source rows. The eight recurrences link four physical " +
                        "chains in each action. Inserting k is a marked extension of the physical occurrence set, " +
                        "and its fresh A cancels the exact -A total of inherited new labels. The adaptive native " +
                        "mask is an integral allocation of these same orbit labels compatible with both strips. " +
                        "For delta=1 the critical lower seam has z*(2S3)=x(y+1)-xz^3-xz-z^3-z^2-2z; y>=2z^3,x>=2z " +
                        "imply it is at least z^2(2z-3)(z+1)>0. This explains the 3s+1 threshold independently of " +
                        "large a, while the complete gate proofs keep all other obligations.")),
                    Paragraph(Text(
                        "Attribution: the supplied strengthened threshold and wide ordinary proofs provide the " +
                        "new allocation and exhaustive charts; PacketNormalForm.Source, " +
                        "FirstPeakSecondMaximum.Native, Chambers.Masks, SourceWidth, the pinned packet " +
                        "Checks/strip bridge and marked-ear transport provide reused physical source APIs. " +
                        "EqualLastTwo lies in the opposite b<a region. No literature novelty, general " +
                        "group-action transport, unrestricted second-gap theorem, kernel acceptance or official " +
                        "acceptance is asserted. Lower-a cases with b<2s+1, the other complementary regions " +
                        "and full J/C3.1 remain OPEN."))),
                DescribeRole.Theorem)), []));
}
