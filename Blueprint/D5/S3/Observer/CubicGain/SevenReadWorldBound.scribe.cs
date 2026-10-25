using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class SevenReadWorldBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each positive fixed source width admits at most three complete worlds in a guarded literal seven-reading fiber.",
        H("Complete Seven-Reading World Bound"),
        Blocks(
            Paragraph(Text("A complete original world W=(r,b,d,a) determines P=[[r,b],[r(1-r)/b,1-r]] and the entire polynomial g(s)=a₀+a₁s+a₂s²+a₃s³. Its native domain FullWorld has 0<r<1, b>0 and g nonzero. This is precisely the original positive trace-one rank-one source domain: every c>0 satisfying bc=r(1-r) is the displayed lower-left entry. Ordinary polynomial coefficients are unique, and every nonzero real polynomial of degree at most three occurs.")),
            Paragraph(Text("Let E be either J=[[0,1],[1,0]] or M=[[0,1],[1,1]]. The implementation uses a Boolean e, false for J and true for M. The six actions are J,M,J,M,J,E in chronological order. Starting with Q₀=I, each next product is Qᵢ=EᵢQᵢ₋₁ and each reading is d+g(i)tr(QᵢP). The seven readings use clocks 0 through 6, the same P, the same whole g and the same d. Write F_E(b;A,C,z,Y,p,v) for the set sevenFiber with readings (0,A,C,z,Y,p,v) and the specified source entry b. All observation parameters are real.")),
            Paragraph(Text("Put j=b+r(1-r)/b, T=1+b, U=1+2b and V=1+kb, where k=2 for E=J and k=3 for E=M. The seven literal traces are (1,j,T,j+r,U,j+2r,V). In particular the fifth action here is J. Define K=16TUV, B₀=-dTUV, B₂=(C-d)UV, B₄=(Y-d)TV and B₆=(v-d)TU. Let G₁=5B₀+15B₂-5B₄+B₆, G₃=-B₀+9B₂+9B₄-B₆ and G₅=B₀-5B₂+15B₄+5B₆. Each G is an affine polynomial in d. The polynomial driftPolynomial is H_E=(A-d)G₃G₅-2(z-d)G₁G₅+(p-d)G₁G₃.")),
            Paragraph(Text("The four even rows fix the entire polynomial g by interpolation at 0,2,4,6. They give Kg(1)=G₁, Kg(3)=G₃ and Kg(5)=G₅. The odd rows therefore imply H_E(d)=0 without division by any odd sample. The coefficient of d³ is 16b(1+2b)²(4b³+16b²+5b+8) for J and 192b⁴(3b²+12b+4) for M. These coefficients are positive for every b>0. Thus H_E is a nonzero cubic for every choice of observations.")),
            Describe.Lean(
                DescribeId.Create("cubic-gain-native-drift-multiset-roots"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/SevenReadWorldBound.native_drift_multiset_le_roots"),
                H("Drift multiplicity pays for every complete world"),
                StatementSource.FromAuthor(MultisetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here S is a finite set of distinct complete worlds, D(S) is the multiset of their drifts with repetitions retained, and R(H_E) is the multiset of real roots of H_E with algebraic multiplicity. The multiset inequality compares the count of each real value, rather than only its presence.")),
                    Paragraph(Text("The condition z≠A prevents G₁ and G₃ from both vanishing at a retained drift. If two of G₁,G₃,G₅ are active, their independent affine source traces determine r and j uniquely. At a fixed drift the even rows already determine the whole gain, so this gives one complete world.")),
                    Paragraph(Text("If only G₁ is active, j is fixed and the source equation is r²-r+b(j-b)=0. If only G₃ is active, n=j+r is fixed and the source equation is r²-(1+b)r+b(n-b)=0. Each monic quadratic admits at most two distinct sources. In either case the two vanished gain samples and the corresponding observations give (X-d)² dividing H_E. Hence a drift supporting two complete worlds has root multiplicity at least two. A repeated source root contributes one world. Summing these pointwise capacities gives the multiset inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-gain-seven-read-full-world-bound"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/SevenReadWorldBound.seven_read_world_bound"),
                H("Finite complete-world fiber of size at most three"),
                StatementSource.FromAuthor(BoundStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real-root multiset of a nonzero cubic has total size at most three. Applying the multiset bound to every finite subset of the actual fiber bounds every such subset by three and proves that the whole fiber is finite. This includes the empty fiber.")),
                    Paragraph(Text("The result is separate for each fixed b>0 and each E. It imposes no upper bound on b or c and no restriction on the signs, sample zeros, nonsample roots, repeated roots or degree of g beyond being nonzero and of degree at most three. Zero drift is included. It gives no cardinality bound on the union over b and assumes no genericity or bounded source box."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parms => Seq(F.Id("b"), Comma, F.Id("A"), Comma,
        F.Id("C"), Comma, F.Id("z"), Comma, F.Id("Y"), Comma, F.Id("p"), Comma, F.Id("v"));
    private static Formula Fiber => Call("F", F.Id("E"), Parms);
    private static Formula Guard => Seq(F.Id("b"), Gt, D(0), Sp, Land, Sp,
        F.Id("z"), Neq, Sp, F.Id("A"));
    private static Formula Prefix(Formula body) => Disp(Seq(Forall, Sp, F.Id("E"), Sp,
        InMacro, Sp, OpenBrace, F.Id("J"), Comma, F.Id("M"), CloseBrace, Comma, Sp,
        Forall, Sp, Parms, Sp, InMacro, Sp, Real, Comma, Sp, Guard, Sp, Implies, Sp, body));
    private static Formula MultisetStatement() => Prefix(Seq(Forall, Sp, F.Id("S"),
        Sp, InMacro, Sp, Call("Finset", Seq(Operatorname, Grp(F.Id("OriginalWorld")))), Comma, Sp,
        F.Id("S"), Subseteq, Fiber, Sp, Implies, Sp,
        Call("D", F.Id("S")), Leq, Call("R", Call("H", F.Id("E"), Parms))));
    private static Formula BoundStatement() => Prefix(Seq(Call("Finite", Fiber),
        Sp, Land, Sp, Lvert, Fiber, Rvert, Sp, Leq, D(3)));
}
