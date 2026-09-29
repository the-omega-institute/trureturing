using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ParityKernelSubcoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the sign hypercube, every parity kernel started from the uniform law makes each proper set of "
            + "coordinates an i.i.d. uniform record.",
        H("Proper Coordinate Records of Parity Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hypercube-parity"),
                DeclarationHandle.Create(Module + "parity"),
                H("Parity character"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("chi", F.Id("x")), Eq, Sp, Prod, Underscore, Grp(F.Id("j"), Lt, F.Id("d")), Sp,
                    Sub(F.Id("x"), F.Id("j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a sign vector x in the hypercube {-1, 1}^d, the parity chi(x) is the product of its "
                        + "coordinates, a real number equal to 1 or -1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hypercube-parity-kernel"),
                DeclarationHandle.Create(Module + "parityKernel"),
                H("Parity kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("P"), F.Id("a")), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Eq, Sp,
                    Frac, Grp(D(1), Plus, Call("a", F.Id("x")), Sp, Call("chi", F.Id("y"))),
                    Grp(D(2), Caret, Grp(F.Id("d")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each real profile a on the hypercube defines the transition weights P_a(x, y). Every "
                        + "row sums to one because the parity sums to zero over the hypercube when d >= 1. "
                        + "The weights are nonnegative, hence a Markov kernel, exactly when |a| <= 1; the "
                        + "identities below hold for every real profile."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-record-law"),
                DeclarationHandle.Create(Module + "subcoordinateLaw"),
                H("Coordinate-record law"),
                StatementSource.FromAuthor(RecordLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a coordinate set S and prescribed sign vectors w_0, ..., w_T, the record weight is the "
                        + "total weight, under the uniform start and the kernel P_a, of the paths whose "
                        + "coordinates in S at every time t agree with those of w_t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("proper-coordinate-records-uniform"),
                DeclarationHandle.Create(Module + "subcoordinateLaw_eq"),
                H("Proper coordinate records are i.i.d. uniform"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Sp, Neq, Sp, OpenBrace, D(1), Comma, Dot, Dot, Dot, Comma, Sp, F.Id("d"),
                    CloseBrace, Sp, Rightarrow, Sp,
                    Call("L", F.Id("a"), F.Id("S"), F.Id("T"), F.Id("w")), Eq, Sp,
                    Open, Frac, Grp(D(1)), Grp(D(2), Caret, Grp(Lvert, Sp, F.Id("S"), Rvert)), Close,
                    Caret, Grp(F.Id("T"), Plus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every dimension d, every real profile a, every proper subset S of the "
                            + "coordinates, every horizon T and every record w, the record law equals "
                            + "(2^(-|S|))^(T+1). For |a| <= 1, when P_a is a Markov kernel, this says that the "
                            + "coordinates in S of the chain started from the "
                            + "uniform law form an independent sequence of uniform vectors on {-1, 1}^S. No "
                            + "condition on a is needed; the statement concerns only the proper coordinates.")),
                    Paragraph(Text(
                        "On every fiber that fixes the coordinates of the proper set S the two parity classes "
                            + "have the same number of vertices, since the uniform laws of the two classes have equal "
                            + "proper marginals; hence the parity sums to zero on the fiber. A fiber has 2^(d - |S|) "
                            + "elements, so the kernel mass P_a(x, fiber) equals 2^(-|S|) from every start x. Summing "
                            + "out the last state of the path and inducting on T gives the product formula, with base "
                            + "case the uniform mass of one fiber."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));

    private static Formula RecordLawFormula()
    {
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        return Disp(Seq(
            Call("L", F.Id("a"), F.Id("S"), F.Id("T"), F.Id("w")), Eq, Sp,
            Sum, Underscore, Grp(Sub(x, D(0)), Comma, Dot, Dot, Dot, Comma, Sub(x, F.Id("T"))), Sp,
            Frac, Grp(D(1)), Grp(D(2), Caret, Grp(F.Id("d"))), Sp,
            Prod, Underscore, Grp(t, Lt, F.Id("T")), Sp,
            Sub(F.Id("P"), F.Id("a")), Open, Sub(x, t), Comma, Sp, Sub(x, Seq(t, Plus, D(1))), Close, Sp,
            Prod, Underscore, Grp(t, Leq, Sp, F.Id("T")), Sp,
            Mathbf, Grp(D(1)), Underscore,
            Grp(Sub(x, t), Bar, Underscore, Grp(F.Id("S")), Eq, Sub(F.Id("w"), t), Bar, Underscore,
                Grp(F.Id("S")))));
    }
}
