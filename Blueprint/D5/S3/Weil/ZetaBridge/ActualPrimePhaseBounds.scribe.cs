using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualPrimePhaseBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.";

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), L = F.Id("L");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Explicit bounds for the amplitude and the first and centered second moments of the finite prime-power symbol.",
            H("Actual Prime Phase Bounds"),
            Blocks(
                Paragraph(Text(
                    "Let c>=3 be natural, L=log(c)>0, w(q)=vonMangoldt(q)/sqrt(q), "
                    + "and z(q)=exp(2*pi*I*log(q)/L). Every q in Ico(2,c) is retained, "
                    + "including all prime powers. A(c) is the sum of these nonnegative weights. "
                    + "The moments use the existing actual phases and the factor two per ordered pair.")),
                Describe.Lean(
                    DescribeId.Create("amplitude-le"),
                    DeclarationHandle.Create(Owner + "amplitude_le"),
                    H("A finite amplitude bound with every prime power"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastThree", c), Rightarrow,
                        Call("A", c), Leq, D(2), Sp, Call("sqrt", c), Sp, L))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every natural c>=3, sum_{q in Ico(2,c)} primeWeight(q) "
                        + "is at most 2*sqrt(c)*log(c). The von Mangoldt bound gives "
                        + "w(q)<=L/sqrt(q). For q>=2, 1/sqrt(q) is at most "
                        + "2*(sqrt(q)-sqrt(q-1)); summing telescopes to "
                        + "2*(sqrt(c-1)-1)<=2*sqrt(c). The sum does not discard prime powers."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The phase estimates bound the actual chord denominators. "
                    + "For 0<=t<=L and e<=min(t,L-t), the chord "
                    + "abs(1-exp(2*pi*I*t/L))=2*abs(sin(pi*t/L)) is at least 4*e/L. "
                    + "The two halves of the period use sin(x)>=2*x/pi on [0,pi/2]. "
                    + "The logarithmic inequality (y-x)/y<=log(y)-log(x), for positive x,y, "
                    + "pays the integer gaps and the gaps at both ends of the period.")),
                Describe.Lean(
                    DescribeId.Create("first-moment-le"),
                    DeclarationHandle.Create(Owner + "firstMoment_le"),
                    H("The actual first moment"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastThree", c), Rightarrow,
                        Call("primeFirstMoment", c), Leq,
                        c, Sp, Call("sqrt", c), Sp, L, Caret, Grp(D(2))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every natural c>=3, primeFirstMoment(c)<=c*sqrt(c)*L^2. "
                        + "For every label 2<=q<c, both log(q) and L-log(q) are at least 1/c. "
                        + "Thus norm(1-z(q))>=4/(c*L). Each exact first-moment term "
                        + "2*abs(w(q))/norm(1-z(q)) is at most (c*L/2)*w(q). "
                        + "Summation and the amplitude bound yield the result."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("offset-le"),
                    DeclarationHandle.Create(Owner + "offset_le"),
                    H("The centered second-moment offset with ordered resonances"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastThree", c), Rightarrow,
                        Call("offset", c), Leq,
                        c, Sp, Grp(D(2), Sp, c, Plus, D(1)), Sp, L, Caret, Grp(D(3))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural c>=3, offset(c)<=c*(2*c+1)*L^3. "
                            + "Distinct-label differences have chord at least 4/(c*L), "
                            + "in either orientation, including wraparound. Hence primeCross "
                            + "is at most (c*L/2)*A(c)^2. For p*q!=c, the sum chord is at "
                            + "least 4/((c+1)*L), and sumCross is at most ((c+1)*L/2)*A(c)^2.")),
                        Paragraph(Text(
                            "For t=log(p)+log(q), the distances to 0, L and 2*L are all paid. "
                            + "Below resonance p*q<=c-1 gives L-t>=1/c. Above resonance "
                            + "p*q>=c+1 gives t-L>=log(c+1)-log(c)>=1/(c+1). "
                            + "The endpoint gaps follow from the first-phase gaps. All ordered "
                            + "p*q=c pairs, including p=q, remain in resonantMass and in the "
                            + "unchanged mean. Only the corresponding sumCross terms vanish. "
                            + "The identity offset=(primeCross+sumCross)/2 and A(c)^2<=4*c*L^2 "
                            + "give the bound. These inequalities supply arithmetic estimates; "
                            + "they do not identify a physical operator or prove RH."))),
                    DescribeRole.Theorem))));
    }
}
