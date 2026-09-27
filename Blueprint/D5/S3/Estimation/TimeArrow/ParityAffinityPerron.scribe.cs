using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ParityAffinityPerronDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ParityAffinityPerron.";

    private static readonly Formula B = F.Id("b"), Dm = F.Id("d"), Hh = F.Id("h");
    private static readonly Formula P = F.Id("p"), X = F.Id("x"), Y = F.Id("y"), Z = F.Id("z");
    private static readonly Formula EtaPlus = Sub(F.Id("eta"), Plus);
    private static readonly Formula EtaMinus = Sub(F.Id("eta"), Minus);
    private static readonly Formula UPlus = Sub(F.Id("u"), Plus);
    private static readonly Formula UMinus = Sub(F.Id("u"), Minus);
    private static readonly Formula VPlus = Sub(F.Id("v"), Plus);
    private static readonly Formula VMinus = Sub(F.Id("v"), Minus);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two parity-class affinities determine a unique positive scalar root and an explicit positive "
            + "eigenvector of the geometrically symmetrized parity kernel.",
        H("Parity Affinities and the Positive Perron Vector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-class"),
                DeclarationHandle.Create(Module + "parityClass"),
                H("Parity classes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("C"), P), Sp, Eq, Sp, OpenBrace, X, Sp, Mid, Sp,
                    Call("chi", X), Sp, Eq, Sp, P, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The class C_p consists of the sign vectors whose parity character equals the real sign p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("class-affinity"),
                DeclarationHandle.Create(Module + "classAffinity"),
                H("Class affinity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("eta"), P), Open, B, Close, Sp, Eq, Sp,
                    Frac,
                    Grp(Sum, Underscore, Grp(X, Sp, InMacro, Sp, Sub(F.Id("C"), P)), Sp,
                        Sqrt, Grp(D(1), Sp, Minus, Sp, Call("b", X), Caret, Grp(D(2)))),
                    Grp(D(2), Caret, Grp(Dm, Sp, Minus, Sp, D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The affinity of a parity class is the normalized cross product of its positive and negative "
                        + "square-root vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-class-vector"),
                DeclarationHandle.Create(Module + "classU"),
                H("Positive square-root vector"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("u"), P), Open, X, Close, Sp, Eq, Sp,
                    Indicator(Sub(F.Id("C"), P), X), Sp,
                    Sqrt, Grp(D(1), Sp, Plus, Sp, Call("b", X))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vector u_p is supported on C_p and has coordinate sqrt(1+b(x)) there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-class-vector"),
                DeclarationHandle.Create(Module + "classV"),
                H("Negative square-root vector"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("v"), P), Open, X, Close, Sp, Eq, Sp,
                    Indicator(Sub(F.Id("C"), P), X), Sp,
                    Sqrt, Grp(D(1), Sp, Minus, Sp, Call("b", X))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vector v_p is supported on C_p and has coordinate sqrt(1-b(x)) there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("affinity-kernel"),
                DeclarationHandle.Create(Module + "affinityKernel"),
                H("Geometric symmetrization"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("R"), Open, X, Comma, Sp, Y, Close, Sp, Eq, Sp,
                    Sqrt, Grp(
                        Sub(F.Id("P"), Seq(F.Id("chi"), B)), Open, X, Comma, Sp, Y, Close,
                        Sp, Sub(F.Id("P"), Seq(F.Id("chi"), B)), Open, Y, Comma, Sp, X, Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The affinity kernel is the entrywise geometric mean of the parity kernel and its transpose, "
                        + "with profile x mapped to chi(x)b(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("explicit-perron-vector"),
                DeclarationHandle.Create(Module + "affinityPerronVector"),
                H("Explicit four-vector"),
                StatementSource.FromAuthor(PerronVectorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The candidate vector is the prescribed positive linear combination of the four class-supported "
                        + "square-root vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("affinity-equation-root"),
                DeclarationHandle.Create(Module + "affinityEquation_unique_root"),
                H("Unique positive affinity root"),
                StatementSource.FromAuthor(AffinityRootFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive eta_+ and eta_- at most one, the quartic affinity equation has a root in "
                            + "(0,1], and every positive root equals it.")),
                    Paragraph(Text(
                        "The difference of the two sides is negative at zero and nonnegative at one. Continuity "
                            + "gives a root, while the quotient of the left side by the right side is strictly "
                            + "increasing on the positive half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affinity-perron-vector"),
                DeclarationHandle.Create(Module + "affinity_perronVector"),
                H("Positive eigenvector from the affinity root"),
                StatementSource.FromAuthor(PerronTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume d is positive, the profile has absolute value below one, and its sum vanishes on "
                            + "each parity class. Let eta_+ and eta_- be the two class affinities, and let z be a positive "
                            + "root of the affinity equation.")),
                    Paragraph(Text(
                        "The frozen proper-coordinate law at the empty coordinate set gives zero total parity, so "
                            + "both classes have 2^(d-1) vertices. The zero sums then give the two squared norms and "
                            + "the class cross products. These identities evaluate the rank-four action of R, and "
                            + "the root equation supplies the final coefficient identity. Every surviving square "
                            + "root and every coefficient is positive, so h is entrywise positive and has eigenvalue "
                            + "(1+z)/2."))),
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

    private static Formula Indicator(Formula set, Formula argument) => Seq(
        Mathbf, Grp(D(1)), Underscore, Grp(set), Open, argument, Close);

    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula RootEquation(Formula root) => Seq(
        root, Caret, Grp(D(2)), Open, D(1), Sp, Plus, Sp, root, Close, Caret, Grp(D(2)),
        Sp, Eq, Sp,
        Open, root, Sp, Plus, Sp, EtaPlus, Caret, Grp(D(2)), Close,
        Open, root, Sp, Plus, Sp, EtaMinus, Caret, Grp(D(2)), Close);

    private static Formula PerronVectorFormula() => Disp(Seq(
        Hh, Sp, Eq, Sp,
        Frac, Grp(EtaPlus, Open, EtaMinus, Caret, Grp(D(2)), Sp, Plus, Sp, Z, Close), Grp(Z),
        Sp, UPlus, Sp, Plus, Sp,
        Frac, Grp(EtaMinus, Z, Open, D(1), Sp, Plus, Sp, Z, Close), Grp(Z),
        Sp, UMinus, Sp, Plus, Sp,
        Open, EtaMinus, Caret, Grp(D(2)), Sp, Plus, Sp, Z, Close, VPlus, Sp, Plus, Sp,
        Z, Open, D(1), Sp, Plus, Sp, Z, Close, VMinus));

    private static Formula AffinityRootFormula()
    {
        Formula w = F.Id("w");
        return Disp(Seq(
            D(0), Sp, Lt, Sp, EtaPlus, Sp, Leq, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, EtaMinus, Sp, Leq, Sp, D(1), Sp, Rightarrow, Sp,
            Exists, Sp, Z, Comma, Sp,
            D(0), Sp, Lt, Sp, Z, Sp, Leq, Sp, D(1), Sp, Land, Sp,
            RootEquation(Z), Sp, Land, Sp,
            Forall, Sp, w, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, w, Sp, Land, Sp, RootEquation(w), Close,
            Sp, Rightarrow, Sp, w, Sp, Eq, Sp, Z));
    }

    private static Formula PerronTheoremFormula()
    {
        Formula zeroPlus = Seq(Sum, Underscore, Grp(X, Sp, InMacro, Sp, Sub(F.Id("C"), Plus)),
            Sp, Call("b", X), Sp, Eq, Sp, D(0));
        Formula zeroMinus = Seq(Sum, Underscore, Grp(X, Sp, InMacro, Sp, Sub(F.Id("C"), Minus)),
            Sp, Call("b", X), Sp, Eq, Sp, D(0));
        Formula eigen = Seq(
            Sum, Underscore, Grp(Y), Sp, F.Id("R"), Open, X, Comma, Sp, Y, Close, Call("h", Y),
            Sp, Eq, Sp, Frac, Grp(D(1), Sp, Plus, Sp, Z), Grp(D(2)), Call("h", X));
        return Disp(Seq(
            D(1), Sp, Leq, Sp, Dm, Sp, Land, Sp,
            Forall, Sp, X, Comma, Sp, Abs(Call("b", X)), Sp, Lt, Sp, D(1), Sp, Land, Sp,
            zeroPlus, Sp, Land, Sp, zeroMinus, Sp, Land, Sp,
            EtaPlus, Sp, Eq, Sp, Sub(F.Id("eta"), Plus), Open, B, Close, Sp, Land, Sp,
            EtaMinus, Sp, Eq, Sp, Sub(F.Id("eta"), Minus), Open, B, Close, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Z, Sp, Land, Sp, RootEquation(Z), Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, X, Comma, Sp, D(0), Sp, Lt, Sp, Call("h", X), Close,
            Sp, Land, Sp, Open, Forall, Sp, X, Comma, Sp, eigen, Close));
    }
}
