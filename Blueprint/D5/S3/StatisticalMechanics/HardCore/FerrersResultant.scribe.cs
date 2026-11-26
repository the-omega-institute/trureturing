using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class FerrersResultantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/FerrersResultant.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Zeros/tahoangnguyen2026ferrers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Ferrers graph is closed stable exactly when all coefficients of its pair-sum resultant are nonnegative.",
        H("Stability of Ferrers independence polynomials"),
        Blocks(
            Node("exponent", "rowExponent", "Number of free vertices",
                Seq(E(), Eq, Par(Seq(F.Id("n"), Minus, D(1), Minus, F.Id("i"))), Plus,
                    Par(Seq(F.Id("m"), Minus, RowLength()))),
                "With zero-based i, the two differences count later rows and columns outside the selected row's neighborhood. The differences are natural subtractions.",
                DescribeRole.Definition),
            Node("polynomial", "explicitPolynomial", "Polynomial from row lengths",
                Seq(Eval("P", "X"), Eq, Pow(Par(Seq(D(1), Plus, F.Id("X"))), F.Id("m")),
                    Plus, F.Id("X"), Sum, Underscore, Grp(F.Id("i")),
                    Pow(Par(Seq(D(1), Plus, F.Id("X"))), E())),
                "The first summand selects columns only. Every other summand selects its least row and any subset of the free vertices.",
                DescribeRole.Definition),
            Node("degree", "degreeBound", "Largest available cardinality",
                Seq(F.Id("d"), Eq, Call(Seq(Operatorname, Grp(F.Id("max"))), F.Id("m"),
                    Seq(Max, Underscore, Grp(F.Id("i")), Par(Seq(E(), Plus, D(1)))))),
                "Take the maximum over the column-only case and all choices of least row. The maximum of the empty row family is zero.",
                DescribeRole.Definition),
            Node("claim", "claim", "Partition criterion",
                Criterion(),
                "For every positive row count n, let λ be nonincreasing with positive entries and put m = λ₀. Use G for the Ferrers graph, p for its actual independence polynomial, N(j) for the number of actual independent j-sets, P for the row-length formula, d for the maximum above, and r for the pair-sum resultant of P. The scan S tests every integer index from zero through d², inclusive.",
                DescribeRole.Definition),
            Node("result", "result", "Exact answer to Question 4.1",
                Criterion(),
                "The least-row count identifies p with P and gives the coefficients. A maximal term contributes positively at degree d. A root of p in the open right half-plane would produce a positive real resultant root by conjugate pairing. When the scan passes, a zero pair sum has both real parts zero, so the constant coefficient detects the imaginary axis. The empty independent set gives p(0) equal to one.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ta-hoang-nguyen-2026-ferrers-question-4-1"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ferrers-stability-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Criterion() => new Formula.Aligned([
        Seq(F.Id("p"), Eq, F.Id("P"), Land,
            Par(Seq(Forall, Sp, F.Id("j"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Coeff("X", F.Id("j"), "p"), Eq, Eval("N", "j"))), Land, Sp, Call(F.Id("N"), D(0)), Eq, D(1), Land),
        Seq(Par(Seq(Forall, Sp, F.Id("j"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Call(F.Id("N"), Seq(F.Id("j"), Plus, D(1))), Eq,
                Choose(F.Id("m"), Seq(F.Id("j"), Plus, D(1))), Plus,
                Sum, Underscore, Grp(F.Id("i")), Choose(E(), F.Id("j")))), Land),
        Seq(D(0), Lt, Sp, F.Id("d"), Land, Op("deg", "p"), Eq, F.Id("d"), Land,
            D(0), Lt, Op("lc", "p"), Land, Op("deg", "r"), Eq, Pow(F.Id("d"), D(2)), Land,
            Op("lc", "r"), Eq, Pow(Par(Op("lc", "p")), Seq(D(2), F.Id("d"))), Land),
        Seq(Par(Seq(Par(Seq(Forall, Sp, F.Id("z"), InMacro, Complexes(), Comma, Sp,
                Eval("p", "z"), Eq, D(0), Implies, Re, Sp, F.Id("z"), Le, D(0))), Iff, Sp, F.Id("S"))), Land),
        Seq(Par(Seq(F.Id("S"), Implies, Par(Seq(Coeff("T", D(0), "r"), Eq, D(0), Iff,
            Par(Seq(Exists, Sp, F.Id("z"), InMacro, Complexes(), Comma, Sp,
                Eval("p", "z"), Eq, D(0), Land, Re, Sp, F.Id("z"), Eq, D(0))))))), Land,
            Coeff("X", D(0), "p"), Eq, D(1)),
        Seq(F.Id("S"), Iff, Par(Seq(Forall, Sp, D(0), Le, Sp, F.Id("j"), Le, Sp, Pow(F.Id("d"), D(2)),
            Comma, Sp, D(0), Le, Coeff("T", F.Id("j"), "r"))))
    ]);

    private static Formula Par(Formula content) => Seq(Open, content, Close);
    private static Formula Pow(Formula bas, Formula exponent) => Seq(bas, Caret, Grp(exponent));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Eval(string p, string z) => Call(F.Id(p), F.Id(z));
    private static Formula Op(string name, string argument) => Call(Seq(Operatorname, Grp(F.Id(name))), F.Id(argument));
    private static Formula Coeff(string variable, Formula index, string polynomial) =>
        Seq(OpenBracket, Pow(F.Id(variable), index), CloseBracket, F.Id(polynomial));
    private static Formula E() => Seq(F.Id("e"), Underscore, Grp(F.Id("i")));
    private static Formula RowLength() => Seq(LambdaLower, Underscore, Grp(F.Id("i")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Choose(Formula n, Formula k) =>
        Call(Seq(Operatorname, Grp(F.Id("choose"))), n, k);
}
