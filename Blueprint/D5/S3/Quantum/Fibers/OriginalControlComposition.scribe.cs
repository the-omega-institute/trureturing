using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalControlCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary finite original controls admit exact chronological concatenation.",
        H("Composition of Original Controls"),
        Blocks(Describe.Lean(
            DescribeId.Create("concatenate-original"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlComposition.concatenate_original"),
            H("Exact control and integral composition"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The base b and its positive probability fiber J(b) are those of FiniteRectangleTransport. OriginalControl(b,T,k,chi) requires a finite nonnegative duration, continuity of both real controls on [0,T], k(t) in J(b), finite variation of chi, and either absolute continuity of both controls or continuous finite piecewise C1 controls. A finite piecewise C1 partition may contain repeated times; on every open piece both derivatives agree with continuous rates on the corresponding closed piece.")),
                Paragraph(Text("Write J(T,f,g)(x)=f(x) for x<=T and J(T,f,g)(x)=f(T)+g(x-T)-g(0) for x>T. The same relative second path is therefore applied after the first, with its real phase lift translated to the terminal phase. The probability coordinates agree at the join. Neither path is replaced or reparameterized.")),
                Paragraph(Text("In the formula below OC abbreviates OriginalControl. Prefix equality is equality on [0,T]. The scalar readout I(F,k,chi,L) denotes the integral from zero to L of F(k(t))*chi prime(t). All functions F continuous on the original open probability fiber are included. The theorem asserts the original control condition, both prefix equalities, both exact tail equations, the exact real phase increment, and additive scalar readouts.")),
                Paragraph(Text("A finite piecewise C1 coordinate is absolutely continuous on its complete finite interval. To see this, its derivative is integrable on each piece. Truncating the partition at any intermediate time, applying the interval fundamental theorem on each nonempty truncated piece, and telescoping reconstructs the coordinate as its initial value plus the integral of its derivative. Empty pieces contribute zero. The integral primitive is absolutely continuous. This covers both original alternatives and pairs using different alternatives.")),
                Paragraph(Text("For two absolutely continuous coordinates, paste the derivatives at T and integrate. The resulting primitive equals the first coordinate on [0,T] and the translated second coordinate on [T,T+S]. It gives continuity at the join and finite variation. Strict probability support follows separately from the original first and second paths. The additive readout follows by splitting the interval integral at T, using local derivative equality on each open piece, and translating the second integration interval. Junction values do not affect the integral.")),
                Paragraph(Text("Both zero durations are included. For a pair of loops at one fixed base height, the probability coordinate still begins and ends at that height. If the two exact real phase increments are 2*pi*m and 2*pi*n, the resulting winding is m+n. Taking F to be each original phase-weight component gives additive five-coordinate residuals; taking F(k)=k gives additive signed area. A compatible initial five-phase lift stays compatible under the original transported integral lift. These consequences retain the actual arbitrary controls and their real winding, rather than only their endpoint circle classes."))),
            DescribeRole.Theorem))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Apply(Formula f, Formula t) => Seq(f, Open, t, Close);
    private static Formula Statement()
    {
        Formula b=F.Id("b"), t=F.Id("T"), s=F.Id("S"), k=F.Id("k"), chi=F.Id("chi");
        Formula kk=F.Id("K"), cc=F.Id("C"), x=F.Id("x"), f=F.Id("F");
        Formula j(Formula a, Formula c) => Call("J",t,a,c);
        Formula interval(Formula end) => Seq(OpenBracket,D(0),Comma,end,CloseBracket);
        Formula integral(Formula a, Formula c, Formula end) => Call("I",f,a,c,end);
        Formula prefix(Formula a, Formula c) => Call("EqOn",a,c,interval(t));
        return Disp(Seq(
            Begin,Grp(F.Id("gathered")),
            Forall,Sp,b,Colon,Call("Base"),Comma,Sp,t,Comma,s,InMacro,Sp,R,Comma,Sp,
            k,Comma,chi,Comma,kk,Comma,cc,Colon,Seq(R,To,Sp,R),Comma,RowBreak,Grp(),
            Call("OC",b,t,k,chi),Land,Sp,Call("OC",b,s,kk,cc),Land,Sp,
            Apply(k,t),Eq,Apply(kk,D(0)),Rightarrow,RowBreak,Grp(),
            Call("OC",b,Seq(t,Plus,s),j(k,kk),j(chi,cc)),Land,Sp,
            prefix(j(k,kk),k),Land,Sp,prefix(j(chi,cc),chi),Land,RowBreak,Grp(),
            Open,Forall,Sp,x,InMacro,Sp,interval(s),Comma,Sp,
            Apply(j(k,kk),Seq(t,Plus,x)),Eq,Apply(kk,x),Land,Sp,
            Apply(j(chi,cc),Seq(t,Plus,x)),Eq,
            Apply(chi,t),Plus,Apply(cc,x),Minus,Apply(cc,D(0)),Close,Land,RowBreak,Grp(),
            Apply(j(chi,cc),Seq(t,Plus,s)),Minus,Apply(j(chi,cc),D(0)),Eq,
            Apply(chi,t),Minus,Apply(chi,D(0)),Plus,Apply(cc,s),Minus,Apply(cc,D(0)),Land,RowBreak,Grp(),
            Open,Forall,Sp,f,Colon,Seq(R,To,Sp,R),Comma,Sp,
            Call("ContinuousOn",f,Call("J",b)),Rightarrow,Sp,
            integral(j(k,kk),j(chi,cc),Seq(t,Plus,s)),Eq,
            integral(k,chi,t),Plus,integral(kk,cc,s),Close,
            End,Grp(F.Id("gathered"))));
    }
}
