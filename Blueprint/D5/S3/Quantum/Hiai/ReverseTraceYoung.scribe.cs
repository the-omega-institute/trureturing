using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class ReverseTraceYoungDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reverse trace Young and its attained minimum for noncommuting positive definite matrices.",
        H("ReverseTraceYoung"), Blocks(
            Describe.Lean(DescribeId.Create("reverse-trace-young"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ReverseTraceYoung.reverse_trace_young"),
                H("Unconditional reverse trace Young"), StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("For positive definite complex M and W and every real a >= 1, "
                    + "a times Re Tr(M to exponent 1/a) is at most Re Tr(M W to exponent 1-a) "
                    + "plus (a-1) Re Tr W. Powers are spectral continuous functional calculus. "
                    + "No commutation, nonempty dimension, or strictly positive trace is assumed.")),
                    Paragraph(Text("For a > 1 factor M to exponent one half as U V, with "
                    + "U = M to exponent one half times W to exponent (1-a)/2 and "
                    + "V = W to exponent (a-1)/2. Apply general Schatten Holder at "
                    + "r=2/a, p=2, q=2/(a-1), allowing positive exponents below one. "
                    + "The original norm_rpow_gram API identifies the three spectral traces. "
                    + "Trace cyclicity gives the mixed trace from U* U; it is nonnegative "
                    + "without asserting that M W to exponent 1-a is selfadjoint. Weighted "
                    + "AM-GM with weights 1/a and (a-1)/a finishes the proof. At a=1 "
                    + "split first: the identity avoids division by a-1.")),
                    Paragraph(Text("This is a classical tracial Young derivation using the "
                    + "attributed physlib Schatten Holder supplier, Apache-2.0. It supplies "
                    + "the variational step in the Carlen-Lieb path; it does not establish "
                    + "operator convexity or solve Hiai Problem 5.18."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("minimum-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ReverseTraceYoung.minimum_and_attainment"),
                H("Explicit attained minimum"), StatementSource.FromAuthor(Minimum()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("The positive definite W0 = M to exponent 1/a "
                    + "attains objective a M W0 = a tracePower (1/a) M and has objective "
                    + "at most that of every positive definite W. The same-base CFC "
                    + "power composition proves M W0 to exponent 1-a = W0. "
                    + "At a=1 all positive definite W attain equality. No attained "
                    + "positive definite optimizer is asserted for singular M.")),
                    Paragraph(Text("CarlenLiebConvexity consumes this exact optimizer at "
                    + "both endpoints, together with the dimension-independent power "
                    + "convexity on the full positive cone, public Jensen perspective "
                    + "and its trace transport. The positive definite mixture of the "
                    + "endpoint optimizers supplies the convexity comparison. "
                    + "Hiai still needs mean-trace concavity, inverse-mean "
                    + "identification, full parameter assembly and its support-constrained "
                    + "semidefinite extension."))), DescribeRole.Theorem))));

    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Domain() => Seq(Forall, Sp, F.Id("u"), Colon, Sp,
        Call("Level"), Comma, Sp, F.Id("d"), Colon, Sp, Call("Type", F.Id("u")), Comma,
        Sp, OpenBracket, Call("Fintype", F.Id("d")), CloseBracket, Comma, Sp,
        OpenBracket, Call("DecidableEq", F.Id("d")), CloseBracket, Comma, Esc);
    private static Formula Mat() => Call("Matrix", F.Id("d"), F.Id("d"),
        Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Value() => Seq(F.Id("a"), Call("tracePower", Frac(D(1), F.Id("a")), F.Id("M")));
    private static Formula Bound() => Seq(Domain(), F.Id("M"), Comma, Sp, F.Id("W"), Colon, Sp,
        Mat(), Comma, Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc,
        Call("PosDef", F.Id("M")), Land, Sp, Call("PosDef", F.Id("W")), Land, Sp,
        D(1), Le, Sp, F.Id("a"), Implies, Esc,
        Value(), Le, Call("objective", F.Id("a"), F.Id("M"), F.Id("W")));
    private static Formula Minimum() => Seq(Domain(), F.Id("M"), Colon, Sp, Mat(), Comma, Sp,
        F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc,
        Call("PosDef", F.Id("M")), Land, Sp, D(1), Le, Sp, F.Id("a"), Implies, Esc,
        Exists, Sp, F.Id("W0"), Colon, Sp, Mat(), Comma, Esc,
        Call("PosDef", F.Id("W0")), Land, Sp, F.Id("W0"), Eq,
        Call("rpow", F.Id("M"), Frac(D(1), F.Id("a"))), Land, Sp,
        Call("objective", F.Id("a"), F.Id("M"), F.Id("W0")), Eq, Value(), Land, Esc,
        Open, Forall, Sp, F.Id("W"), Colon, Sp, Mat(), Comma, Sp,
        Call("PosDef", F.Id("W")), Implies, Sp,
        Call("objective", F.Id("a"), F.Id("M"), F.Id("W0")), Le,
        Call("objective", F.Id("a"), F.Id("M"), F.Id("W")), Close);
}
