using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciLiftTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciLiftTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "For an odd prime, the two normalized return coordinates obey "
                + "one trace relation. A single Fibonacci quotient therefore decides "
                + "whether the least period is retained at the prime square.",
            H("Scalar Fibonacci Lift Obstruction"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fibonacci-quotient-trace"),
                    DeclarationHandle.Create(Prefix + "quotient_trace_identity"),
                    H("The exact integral trace correction"),
                    StatementSource.FromAuthor(TraceFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let p be prime with p different from 2, r=period(p), "
                                + "a=F(r)/p and b=(F(r+1)-1)/p. The determinant of "
                                + "the actual companion power first forces r to be even. "
                                + "The integral determinant identity then gives "
                                + "2*b-a=-p*(b*b-a*b-a*a). Cancellation by p occurs "
                                + "in the integers, never in ZMod(p^2).")),
                        Paragraph(Text(
                            "quotient_trace_zero transports this identity to ZMod(p). "
                                + "It explains why the normalized matrix [[b,a],[a,b-a]] "
                                + "has only one free residue at the first lift."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fibonacci-single-quotient-criterion"),
                    DeclarationHandle.Create(Prefix + "square_period_eq_iff_firstQuotient"),
                    H("One residue decides the exceptional lift"),
                    StatementSource.FromAuthor(Criterion()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The hypotheses are exactly primality and p different from 2. "
                                + "The ramified prime 5 is included. A nonzero first "
                                + "quotient proves the full p-fold lift by "
                                + "full_lift_of_firstQuotient_nonzero. No prime-class "
                                + "nonvanishing or global Wall-Sun-Sun existence claim "
                                + "is assumed or obtained."))),
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

    private static Formula TraceFormula() => Disp(Seq(
        Call("sub", Seq(F.Id("2"), Cdot, F.Id("b")), F.Id("a")),
        Sp, Eq, Sp,
        Call("neg", Seq(F.Id("p"), Cdot,
            Call("sub", Call("sub", Call("square", F.Id("b")),
                Seq(F.Id("a"), Cdot, F.Id("b"))), Call("square", F.Id("a")))))));

    private static Formula Criterion() => Disp(Call("Iff",
        Seq(Call("period", Call("square", F.Id("p"))), Sp, Eq, Sp,
            Call("period", F.Id("p"))),
        Call("divides", F.Id("p"), Call("firstQuotient", F.Id("p"),
            Call("period", F.Id("p"))))));
}
