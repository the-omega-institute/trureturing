using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class PermanentFinitePredictionObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite autonomous predictor cannot maintain a fixed subunit error forever on an irrational circle rotation.",
        H("Permanent Finite-Prediction Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-permanent-finite-prediction"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/PermanentFinitePredictionObstruction."
                        + "no_permanent_finite_prediction"),
                H("No finite autonomous predictor is permanently accurate"),
                StatementSource.FromAuthor(PermanentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let S be a finite state type with an autonomous update G, a complex readout h, "
                        + "and an actual initial state. Fix a phase x on AddCircle 1 and an irrational "
                        + "real increment alpha. If the readout along the finite orbit stayed within "
                        + "epsilon of the rotated phase at every natural time, where 0 < epsilon < 1/2, "
                        + "then the finite-horizon arithmetic bound would hold for every horizon H. "
                        + "Choosing a natural H strictly larger than that fixed bound gives a contradiction. "
                        + "Thus no such finite autonomous predictor can satisfy the subunit error bound forever."))),
                DescribeRole.Theorem))));

    private static Formula Circle() => Seq(Operatorname, Grp(F.Id("AddCircle")), Open, D(1), Close);

    private static Formula Accuracy()
    {
        Formula n = F.Id("n");
        Formula predicted = Seq(F.Id("h"), Open, F.Id("G"), Caret, Grp(n), Open,
            F.Id("s"), Underscore, Grp(D(0)), Close, Close);
        Formula target = Seq(Open, F.Id("x"), Plus, n, F.Id("alpha"), Close);
        return Seq(Forall, Sp, n, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Vert, Sp, predicted, Minus, target, Vert, Leq, Sp, F.Id("epsilon"));
    }

    private static Formula PermanentFormula() => Disp(Seq(
        Forall, Sp, F.Id("S"), Comma, Sp, OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp,
        F.Id("S"), CloseBracket, Comma, Sp,
        Forall, Sp, F.Id("G"), Colon, F.Id("S"), To, Sp, F.Id("S"), Comma, Sp,
        F.Id("h"), Colon, F.Id("S"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
        F.Id("s"), Underscore, Grp(D(0)), InMacro, Sp, F.Id("S"), Comma, Sp,
        F.Id("x"), InMacro, Sp, Circle(), Comma, Sp,
        F.Id("alpha"), Comma, Sp, F.Id("epsilon"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Operatorname, Grp(F.Id("Irrational")), Open, F.Id("alpha"), Close, Sp, Land, Sp,
        D(0), Lt, F.Id("epsilon"), Sp, Land, Sp, F.Id("epsilon"), Lt, Frac, Grp(D(1)), Grp(D(2)), Sp,
        Open, Accuracy(), Close, Sp, Rightarrow, Sp, F.Id("False"), Dot));
}
