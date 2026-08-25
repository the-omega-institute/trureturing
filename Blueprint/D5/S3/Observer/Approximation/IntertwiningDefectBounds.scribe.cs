using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Approximation;

internal sealed class IntertwiningDefectBoundsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Approximation/IntertwiningDefectBounds."
            + "intertwining_defect_propagation_bounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted and uniform norm estimates jointly quantify defect propagation.",
        H("Intertwining Defect Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intertwining-defect-propagation-bounds"),
                DeclarationHandle.Create(Declaration),
                H("Both propagation bounds hold"),
                StatementSource.FromAuthor(BoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct is the weighted finite-sum estimate. The second "
                            + "states that uniform bounds on both evolution operators imply "
                            + "the linear-in-time estimate.")),
                    Paragraph(Text(
                        "Both conjuncts apply the canonical declarations from the existing "
                            + "intertwining-defect family; this module introduces no new "
                            + "mathematical definition."))),
                DescribeRole.Theorem))));

    private static Formula BoundsFormula()
    {
        Formula scalar = F.Id("K");
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula a = F.Id("A");
        Formula c = F.Id("C");
        Formula t = F.Id("T");
        Formula l = F.Id("L");
        Formula n = F.Id("n");
        Formula j = F.Id("j");

        Formula carrierPremises = Seq(
            Call("NontriviallyNormedField", scalar), Sp, Land, Sp,
            Call("SeminormedAddCommGroup", source), Sp, Land, Sp,
            Call("NormedSpace", scalar, source), Sp, Land,
            RowBreak, Grp(),
            Call("SeminormedAddCommGroup", target), Sp, Land, Sp,
            Call("NormedSpace", scalar, target), Sp, Land, Sp,
            TypedMap(a, scalar, target, target), Sp, Land,
            RowBreak, Grp(),
            TypedMap(c, scalar, source, target), Sp, Land, Sp,
            TypedMap(t, scalar, source, source), Sp, Land, Sp,
            l, Sp, InMacro, Sp, F.Id("R"), Sp, Land, Sp,
            n, Sp, InMacro, Sp, F.Id("N"));

        Formula defect = Subtract(Multiply(c, t), Multiply(a, c));
        Formula iterated = Subtract(Multiply(c, Power(t, n)), Multiply(Power(a, n), c));
        Formula weightedTerm = Multiply(
            Multiply(Power(NormOf(a), Seq(n, Minus, D(1), Minus, j)), NormOf(defect)),
            Power(NormOf(t), j));
        Formula weighted = Seq(
            NormOf(iterated), Sp, Leq, Sp,
            Sum, Underscore, Grp(Seq(j, Eq, D(0))), Caret,
            Grp(Seq(n, Minus, D(1))), Sp, weightedTerm);
        Formula uniformPremises = Seq(
            NormOf(a), Sp, Leq, Sp, l, Sp, Land, Sp,
            NormOf(t), Sp, Leq, Sp, l);
        Formula uniform = Seq(
            NormOf(iterated), Sp, Leq, Sp,
            Multiply(Multiply(n, Power(l, Seq(n, Minus, D(1)))), NormOf(defect)));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, source, Comma, Sp, target, Comma, Sp,
            a, Comma, Sp, c, Comma, Sp, t, Comma, Sp, l, Comma, Sp, n, Comma,
            RowBreak, Grp(),
            carrierPremises, Sp, Rightarrow,
            RowBreak, Grp(),
            weighted, Sp, Land,
            RowBreak, Grp(),
            Grp(Seq(uniformPremises, Sp, Rightarrow, Sp, uniform))));
    }

    private static Formula TypedMap(
        Formula map,
        Formula scalar,
        Formula source,
        Formula target) =>
        Seq(map, Sp, InMacro, Sp, Call("ContinuousLinearMap", scalar, source, target));

    private static Formula NormOf(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

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
