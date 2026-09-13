using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciFrobeniusQuotientBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciFrobeniusQuotientBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual return-period quotient is minus the period times the signed Frobenius-index "
            + "quotient. The multiplier is a unit away from characteristics two and five.",
        H("Exact Fibonacci Frobenius Quotient Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quotient-period-eq-frobenius"),
                DeclarationHandle.Create(Prefix + "quotient_period_eq_frobenius"),
                H("Exact quotient transport without equating the indices"),
                StatementSource.FromAuthor(Bridge()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every prime p other than 2 and 5, let epsilon="
                        + "legendreSym(5,p), n=(p-epsilon).toNat, r=period(p), "
                        + "and Q(p,t)=F(t)/p in ZMod(p). Then Q(p,r)=-r*Q(p,n). "
                        + "The sign of epsilon is retained: n=p+1 in the inert case.")),
                    Paragraph(Text("The existing Frobenius theorem proves F(n)=0 and F(p)=epsilon "
                        + "modulo p. The proof compares (phi^r)^n and (phi^n)^r, transports "
                        + "their coefficients modulo p squared, and cancels p in the integers. "
                        + "Evenness of r and n=-epsilon modulo p give the displayed factor. "
                        + "No premise r=n is present."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-period-eq-frobenius-factor-isUnit"),
                DeclarationHandle.Create(Prefix + "quotient_period_eq_frobenius_factor_isUnit"),
                H("The actual proportionality coefficient is invertible"),
                StatementSource.FromAuthor(Call("IsUnit", Call("neg", Call("period", F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof establishes period(p) divides 2*n. Since p is odd "
                        + "and n=-epsilon is nonzero modulo p, p does not divide period(p). "
                        + "The coefficient is -period(p), not a separately selected unit.")),
                    Paragraph(Text("wall_iff_standard_quotient identifies the old-period plateau "
                        + "at p squared with Q(p,n)=0. The higher-power module treats 2 and 5 "
                        + "separately; this theorem does not cancel their nonunit coefficients."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Bridge() => Disp(Seq(
        Call("quotientMod", F.Id("p"), Call("period", F.Id("p"))), Sp, Eq, Sp,
        Call("neg", Call("period", F.Id("p"))), Cdot,
        Call("quotientMod", F.Id("p"), Call("frobeniusIndex", F.Id("p")))));
}
