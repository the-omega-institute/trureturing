using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualColumnRemainderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/ActualColumnRemainder.";
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
        Formula c = F.Id("c"), m = F.Id("m"), n = F.Id("n"), N = F.Id("N");
        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNCOMPILED: faithful author statements; no validated provenance claim.",
            H("Actual Weighted Column Remainder"),
            Blocks(
                Paragraph(Text("The actual weighted first-jet error and infinite paired remainder are owned here. All Lean proofs, Reg selections and Scribe emission await caller-owned verification.")),
                Describe.Lean(
                    DescribeId.Create("weighted-head-mass"),
                    DeclarationHandle.Create(Owner + "weightedHeadMass"),
                    H("The actual weighted absolute head moment"),
                    StatementSource.FromAuthor(Disp(Seq(Call("W", F.Id("S"), F.Id("v")), Eq, Call("SumAbsIndexTimesCoefficientNorm", F.Id("S"), F.Id("v"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. W(S,v)=sum_{n in S} abs(n)*norm(v(n)). S is any finite integer set and v has arbitrary complex values; the n=0 contribution is exactly zero. W is never replaced by A times the unweighted mass."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("paired-remainder-budget"),
                    DeclarationHandle.Create(Owner + "pairedRemainderBudget"),
                    H("The exact paired weighted remainder budget"),
                    StatementSource.FromAuthor(Disp(Seq(Call("R", c, N, F.Id("A"), F.Id("S"), F.Id("v")), Eq, Call("div", Call("mul", D(8), Call("square", Call("arithmeticBoundaryBudget", c)), Call("square", Call("W", F.Id("S"), F.Id("v"))), Call("square", Call("add", N, D(1)))), Call("mul", D(3), Call("square", F.Id("pi")), Call("cube", N), Call("square", Call("sub", Call("add", N, D(1)), F.Id("A")))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. R=8*arithmeticBoundaryBudget(c)^2*W(S,v)^2*(M+1)^2/(3*pi^2*M^3*(M+1-A)^2). Its admitted domain is c>=2, natural M>0, real A>=0, abs(n)<=A for every n in S, and A<M+1. No stronger separation such as M>=2A is used."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("weighted-coupling-first-jet-error"),
                    DeclarationHandle.Create(Owner + "weighted_coupling_first_jet_error"),
                    H("Weighted error of the actual divided-difference column"),
                    StatementSource.FromAuthor(Disp(Seq(Call("And", Call("AtLeastTwo", c), Call("Nonnegative", F.Id("A")), Call("HeadWithin", F.Id("S"), F.Id("A")), Call("Less", F.Id("A"), Call("abs", m))), Rightarrow, Call("LessEqual", Call("norm", Call("ColumnMinusJet", c, F.Id("S"), F.Id("v"), m)), Call("div", Call("mul", D(2), Call("arithmeticBoundaryBudget", c), Call("W", F.Id("S"), F.Id("v"))), Call("mul", F.Id("pi"), Call("abs", m), Call("sub", Call("abs", m), F.Id("A")))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For c>=2, every finite S subset Z, arbitrary v:Z->C, A>=0, abs(n)<=A on S, and integer m with A<abs(m), norm(couplingColumn(c,S,v,m)-couplingFirstJet(c,S,v,m))<=2*arithmeticBoundaryBudget(c)*W(S,v)/(pi*abs(m)*(abs(m)-A)). The proof consumes arithmetic_coupling_first_jet_error at each singleton with radius abs(n), including n=0, compares the positive denominators, and sums the actual differences. It imposes no reality or moment-vanishing premise."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("paired-first-jet-remainder-tail"),
                    DeclarationHandle.Create(Owner + "paired_first_jet_remainder_tail"),
                    H("Infinite paired first-jet remainder with cubic cutoff decay"),
                    StatementSource.FromAuthor(Disp(Seq(Call("And", Call("AtLeastTwo", c), Call("Positive", N), Call("Nonnegative", F.Id("A")), Call("HeadWithin", F.Id("S"), F.Id("A")), Call("Less", F.Id("A"), Call("add", N, D(1)))), Rightarrow, Call("And", Call("Summable", Call("PairedRemainderSequence", c, N, F.Id("S"), F.Id("v"))), Call("LessEqual", Call("PairedRemainderTsum", c, N, F.Id("S"), F.Id("v")), Call("R", c, N, F.Id("A"), F.Id("S"), F.Id("v"))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For every c>=2, natural M>0, real A>=0 with A<M+1 and abs(n)<=A on any finite integer S, and every complex coefficient function v, the sequence norm(Column(m)-Jet(m))^2+norm(Column(-m)-Jet(-m))^2, m=M+j+1, is summable and its genuine tsum is at most R. For t>=M+1, t/(t-A)<=(M+1)/(M+1-A); the one-sign square is bounded by C^2/t^4 with C=2*B*W*(M+1)/(pi*(M+1-A)). The consumed exact owner inverse-fourth partial tail yields 2*C^2/(3*M^3)=R. Both signs and the zero/empty head remain. For fixed head, c and A this budget has cubic cutoff decay. No finite terminal exterior cutoff is asserted."))),
                    DescribeRole.Theorem))));
    }
}
