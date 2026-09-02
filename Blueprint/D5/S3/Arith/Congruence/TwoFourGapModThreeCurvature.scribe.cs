using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TwoFourGapModThreeCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-four-gap constellations omit a residue modulo three exactly when every "
            + "adjacent curvature is nonzero.",
        H("Two-Four-Gap Modulo-Three Curvature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-four-gap-mod-three-admissibility"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/TwoFourGapModThreeCurvature."
                        + "two_four_gap_mod_three_admissible_iff"),
                H("Modulo-three admissibility is equivalent to nonzero gap curvature"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a finite integer constellation whose consecutive gaps are "
                            + "all two or four. Its normalized curvature at a triple is the "
                            + "second gap bit minus the first gap bit.")),
                    Paragraph(Text(
                        "The constellation omits a residue modulo three exactly when every "
                            + "adjacent curvature is nonzero. Equal gaps have zero curvature "
                            + "and their three points cover all residues.")),
                    Paragraph(Text(
                        "A two-then-four turn has curvature one, while a four-then-two turn "
                            + "has curvature minus one. Each unequal turn visits only two "
                            + "residues and therefore has an explicitly omitted residue.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact theorem. The "
                            + "proof constructs the residue trajectory from the integer gaps, "
                            + "proves its two-step repetition, and classifies all four local "
                            + "gap pairs."))),
                DescribeRole.Theorem))));

    private static Formula PointAt(Formula points, Formula index) =>
        new Formula.Subscript(points, index);

    private static Formula Successor(Formula index) =>
        Seq(index, Sp, Plus, Sp, D(1));

    private static Formula SecondSuccessor(Formula index) =>
        Seq(index, Sp, Plus, Sp, D(2));

    private static Formula GapAt(Formula points, Formula index) =>
        Seq(
            PointAt(points, Successor(index)),
            Sp, Minus, Sp, PointAt(points, index));

    private static Formula CurvatureAt(Formula points, Formula index) =>
        Seq(
            Open,
            new Formula.Fraction(GapAt(points, Successor(index)), D(2)),
            Sp, Minus, Sp, D(1),
            Close,
            Sp, Minus, Sp,
            Open,
            new Formula.Fraction(GapAt(points, index), D(2)),
            Sp, Minus, Sp, D(1),
            Close);

    private static Formula ResidueAt(Formula points, Formula index) =>
        Call("residue", D(3), PointAt(points, index));

    private static Formula LocalOmission(Formula points, Formula index, Formula residue) =>
        Seq(
            Exists, Sp, residue, Sp, InMacro, Sp, Call("ZMod", D(3)), Comma, Sp,
            ResidueAt(points, index), Sp, Neq, Sp, residue, Sp, Land, Sp,
            ResidueAt(points, Successor(index)), Sp, Neq, Sp, residue, Sp, Land, Sp,
            ResidueAt(points, SecondSuccessor(index)), Sp, Neq, Sp, residue);

    private static Formula LocalCoverage(Formula points, Formula index, Formula residue) =>
        Seq(
            Forall, Sp, residue, Sp, InMacro, Sp, Call("ZMod", D(3)), Comma, Sp,
            ResidueAt(points, index), Sp, Eq, Sp, residue, Sp, Lor, Sp,
            ResidueAt(points, Successor(index)), Sp, Eq, Sp, residue, Sp, Lor, Sp,
            ResidueAt(points, SecondSuccessor(index)), Sp, Eq, Sp, residue);

    private static Formula TheoremFormula()
    {
        Formula points = F.Id("H");
        Formula index = F.Id("i");
        Formula residue = F.Id("r");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula length = Call("length", points);
        Formula firstBound = Seq(
            index, Sp, Plus, Sp, D(1), Sp, Lt, Sp, length);
        Formula secondBound = Seq(
            index, Sp, Plus, Sp, D(2), Sp, Lt, Sp, length);
        Formula dense = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            firstBound, Sp, Rightarrow, Sp,
            Open,
            GapAt(points, index), Sp, Eq, Sp, D(2), Sp, Lor, Sp,
            GapAt(points, index), Sp, Eq, Sp, D(4),
            Close);
        Formula globalOmission = Seq(
            Exists, Sp, residue, Sp, InMacro, Sp, Call("ZMod", D(3)), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            index, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            ResidueAt(points, index), Sp, Neq, Sp, residue);
        Formula allCurvaturesNonzero = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            secondBound, Sp, Rightarrow, Sp,
            CurvatureAt(points, index), Sp, Neq, Sp, D(0));
        Formula zeroTurn = Seq(
            CurvatureAt(points, index), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            Open,
            GapAt(points, index), Sp, Eq, Sp, GapAt(points, Successor(index)),
            Sp, Land, Sp, LocalCoverage(points, index, residue),
            Close);
        Formula positiveTurn = Seq(
            CurvatureAt(points, index), Sp, Eq, Sp, D(1), Sp, Leftrightarrow, Sp,
            Open,
            GapAt(points, index), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            GapAt(points, Successor(index)), Sp, Eq, Sp, D(4), Sp, Land, Sp,
            LocalOmission(points, index, residue),
            Close);
        Formula negativeTurn = Seq(
            CurvatureAt(points, index), Sp, Eq, Sp, Minus, D(1), Sp,
            Leftrightarrow, Sp,
            Open,
            GapAt(points, index), Sp, Eq, Sp, D(4), Sp, Land, Sp,
            GapAt(points, Successor(index)), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            LocalOmission(points, index, residue),
            Close);
        Formula localClassification = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            secondBound, Sp, Rightarrow,
            RowBreak, Grp(),
            Open,
            Open, zeroTurn, Close, Sp, Land,
            RowBreak, Grp(),
            Open, positiveTurn, Close, Sp, Land,
            RowBreak, Grp(),
            Open, negativeTurn, Close,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, points, Sp, InMacro, Sp, Call("List", integers), Comma,
            RowBreak, Grp(),
            Open, dense, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open,
            Open,
            Open, globalOmission, Close, Sp, Leftrightarrow, Sp,
            allCurvaturesNonzero,
            Close,
            Sp, Land,
            RowBreak, Grp(),
            localClassification,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
