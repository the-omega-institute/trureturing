using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class EvenDenseConstellationMirrorCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even two-four-gap constellation that omits a residue modulo three has a reversal-fixed gap code.",
        H("Even Dense Constellation Mirror Code"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-dense-constellation-gap-code-is-self-reversing"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/EvenDenseConstellationMirrorCode."
                    + "even_dense_constellation_gap_code_self"),
                H("The gap code of an even admissible dense constellation is self-reversing"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let points be an integer constellation whose consecutive gaps are all two or four. "
                            + "If one residue modulo three is omitted, two consecutive gaps cannot agree: "
                            + "three points separated by equal gaps would visit every residue.")),
                    Paragraph(Text(
                        "The constructed Boolean gap code therefore alternates. An even number of points "
                            + "gives the code odd length, so reversing it preserves every symbol."))),
                DescribeRole.Theorem))));

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula PointAt(Formula points, Formula index) =>
        new Formula.Subscript(points, index);

    private static Formula GapAt(Formula points, Formula index) =>
        Seq(
            PointAt(points, Seq(index, Sp, Plus, Sp, D(1))),
            Sp, Minus, Sp, PointAt(points, index));

    private static Formula TheoremFormula()
    {
        Formula points = F.Id("H");
        Formula index = F.Id("i");
        Formula omitted = F.Id("r");
        Formula left = F.Id("u");
        Formula right = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula pointList = Call("List", integers);
        Formula length = Call("length", points);
        Formula indexInRange = Seq(
            index, Sp, Plus, Sp, D(1), Sp, Lt, Sp, length);
        Formula dense = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            indexInRange, Sp, Rightarrow, Sp,
            Open,
            GapAt(points, index), Sp, Eq, Sp, D(2), Sp, Lor, Sp,
            GapAt(points, index), Sp, Eq, Sp, D(4),
            Close);
        Formula omittedResidue = Seq(
            Exists, Sp, omitted, Sp, InMacro, Sp, Call("ZMod", D(3)), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            index, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            Call("residue", D(3), PointAt(points, index)), Sp, Neq, Sp, omitted);
        Formula bitRule = Lambda(
            Seq(left, Comma, Sp, right),
            Call("decide", Seq(right, Sp, Minus, Sp, left, Sp, Eq, Sp, D(4))));
        Formula gapCode = Call("zipWith", bitRule, points, Call("tail", points));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, points, Sp, InMacro, Sp, pointList, Comma,
            RowBreak, Grp(),
            Open,
            Open, dense, Close, Sp, Land, RowBreak, Grp(),
            Open, omittedResidue, Close, Sp, Land, RowBreak, Grp(),
            Call("Even", length),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("reverse", gapCode), Sp, Eq, Sp, gapCode, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
