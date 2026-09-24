using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class FairWindowDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FairWindowDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-parity cycle forces a transport defect, while each proper context is fair.",
        H("A Lower Bound for Deterministic Fair-Input Window Rules"),
        Blocks(
            Node("defect", "A complete defect context", "defect", DefectFormula(),
                "Let sigma send zero to minus one and one to one. A table f maps an R-bit "
                + "word to one bit. For a context v indexed from zero through R, head(v) "
                + "has coordinates v(i), tail(v) has coordinates v(i+1), and last(v) is v(R). "
                + "The indicator is zero when the last relation bit transports the first "
                + "output to the second, and one otherwise. Thus relation zero reverses "
                + "the output and relation one preserves it.", DescribeRole.Definition),
            Node("fair-defect", "The exact fair-input probability", "fairDefect", FairFormula(),
                "All R+1 relation bits are independent and fair. Every complete context "
                + "therefore has mass one over two to the power R+1. This finite average "
                + "is the exact cylinder probability of a defect for the same fixed table "
                + "at consecutive times.", DescribeRole.Definition),
            Node("optimal-fair-defect", "The finite optimum", "optimalFairDefect", MinimumFormula(),
                "The set T(R) of all maps from binary R-words to one bit is finite and "
                + "nonempty. Its minimum defect is attained by a deterministic table.",
                DescribeRole.Definition),
            Node("fair-window-lower-bound", "Every table obeys the lower bound",
                "fair_window_defect_lower_bound", LowerFormula(),
                "Take binary cycles of length R+2 with an odd number of zero relations. "
                + "Deleting any coordinate, after any permutation of the coordinates, "
                + "is a bijection onto all binary words of length R+1: the omitted bit "
                + "is uniquely forced by parity. Permuting coordinates preserves the odd "
                + "parity law by a bijection; in particular its cyclic rotations preserve it. "
                + "Consequently every cyclic defect context, "
                + "including one crossing the seam, has precisely the fair joint law. "
                + "If all defects vanished, multiplying the transport equations around "
                + "the cycle would make the nonzero product of output signs equal its "
                + "negative. Each cycle therefore contributes at least one defect. "
                + "Summing over cycles and positions gives (R+2) times the fair defect "
                + "at least one. The statement also includes R equal to zero. It establishes "
                + "the lower bound; an upper construction and its asymptotics are separate.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Cube(Formula n) => new Formula.Power(Call("Fin", D(2)), Call("Fin", n));
    private static Formula Tables(Formula r) => Seq(Open, Cube(r), To, Call("Fin", D(2)), Close);
    private static Formula PlusN(Formula r, byte n) => Add(r, D(n));
    private static Formula Lower(Formula r) => new Formula.Fraction(D(1), PlusN(r, 2));

    private static Formula DefectFormula()
    {
        var r = F.Id("R"); var f = F.Id("f"); var v = F.Id("v");
        var unequal = new Formula.Relation(Call("sigma", new Formula.Apply(f, [Call("tail", v)])),
            FormulaRelationOperator.NotEqual,
            Multiply(Call("sigma", Call("last", v)),
                Call("sigma", new Formula.Apply(f, [Call("head", v)]))));
        var indicator = Seq(D(1), Underscore, Grp(unequal));
        return Disp(All("R", Nat(), All("f", Tables(r), All("v", Cube(PlusN(r, 1)),
            Eqn(Call("defect", f, v), indicator)))));
    }

    private static Formula FairFormula()
    {
        var r = F.Id("R"); var f = F.Id("f"); var v = F.Id("v");
        var sum = Seq(Sum, Underscore, Grp(v, InMacro, Cube(PlusN(r, 1))), Call("defect", f, v));
        return Disp(All("R", Nat(), All("f", Tables(r),
            Eqn(Call("fairDefect", r, f), new Formula.Fraction(sum, new Formula.Power(D(2), PlusN(r, 1)))))));
    }

    private static Formula MinimumFormula()
    {
        var r = F.Id("R"); var f = F.Id("f");
        return Disp(All("R", Nat(), Eqn(Call("optimalFairDefect", r),
            Seq(Min, Underscore, Grp(f, InMacro, Tables(r)), Call("fairDefect", r, f)))));
    }

    private static Formula LowerFormula()
    {
        var r = F.Id("R"); var f = F.Id("f");
        return Disp(All("R", Nat(), new Formula.Logic(
            All("f", Tables(r), new Formula.Relation(Lower(r), FormulaRelationOperator.LessThanOrEqual,
                Call("fairDefect", r, f))), FormulaLogicOperator.And,
            new Formula.Relation(Lower(r), FormulaRelationOperator.LessThanOrEqual,
                Call("optimalFairDefect", r)))));
    }
}
