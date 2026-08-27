using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DefectComposition;

internal sealed class LinearPostprocessingDefectContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear postprocessing contracts realization defect by its operator norm.",
        H("Linear Postprocessing Defect Contraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-postprocessing-defect-contraction"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/DefectComposition/LinearPostprocessingDefectContraction."
                        + "linear_postprocessing_defect_contraction"),
                H("Postprocessing contracts distance to the realizable image"),
                StatementSource.FromAuthor(ContractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and target are real normed spaces, with the source finite "
                            + "dimensional. The realizable set I is nonempty and closed, and B "
                            + "is a continuous linear postprocessor.")),
                    Paragraph(Text(
                        "Closedness supplies a nearest realizable point to y. Its image under B "
                            + "is an admissible comparison point in image(B,I), and the operator "
                            + "norm bounds the resulting distance.")),
                    Paragraph(Text(
                        "The source also assumes convexity and finite dimensionality of the "
                            + "target. Neither is needed for this conclusion, so the machine "
                            + "statement proves the two public clauses without them."))),
                DescribeRole.Theorem))));

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typeclass(string name, Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, carrier, Close, CloseBracket);

    private static Formula ScalarTypeclass(string name, Formula scalar, Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Underscore, Grp(scalar),
            Open, carrier, Close, CloseBracket);

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

    private static Formula ContractionFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula source = F.Id("Y");
        Formula target = F.Id("Z");
        Formula postprocessor = F.Id("B");
        Formula realizable = F.Id("I");
        Formula point = F.Id("y");
        Formula imageDistance = Call(
            "infDist", Seq(postprocessor, Open, point, Close),
            Call("image", postprocessor, realizable));
        Formula sourceDistance = Call("infDist", point, realizable);
        Formula operatorNorm = new Formula.Norm(postprocessor);
        Formula generalBound = Seq(
            imageDistance, Sp, Leq, Sp, operatorNorm, Sp, sourceDistance);
        Formula contractiveBound = Seq(
            operatorNorm, Sp, Leq, Sp, D(1), Sp, Rightarrow, Sp,
            imageDistance, Sp, Leq, Sp, sourceDistance);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, target, Colon, Sp, Type(), Comma,
            RowBreak, Grp(),
            Typeclass("NormedAddCommGroup", source), Sp,
            ScalarTypeclass("NormedSpace", real, source), Sp,
            ScalarTypeclass("FiniteDimensional", real, source), Comma,
            RowBreak, Grp(),
            Typeclass("NormedAddCommGroup", target), Sp,
            ScalarTypeclass("NormedSpace", real, target), Comma,
            RowBreak, Grp(),
            postprocessor, Colon, Sp, Call("ContinuousLinearMap", real, source, target),
            Comma, Sp, realizable, Colon, Sp, Call("Set", source), Comma, Sp,
            point, Colon, Sp, source, Comma,
            RowBreak, Grp(),
            Open, Call("IsClosed", realizable), Sp, Land, Sp,
            Call("Nonempty", realizable), Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, generalBound, Close, Sp, Land,
            RowBreak, Grp(),
            Open, contractiveBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
