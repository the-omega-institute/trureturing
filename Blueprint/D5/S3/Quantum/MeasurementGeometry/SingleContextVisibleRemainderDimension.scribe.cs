using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.MeasurementGeometry;

internal sealed class SingleContextVisibleRemainderDimensionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension."
            + "single_context_visible_remainder_dimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One rank-one projective context exposes one diagonal slice of the trace-zero "
            + "Hermitian state directions and leaves its orthogonal remainder.",
        H("Single-Context Visible and Remainder Dimensions"),
        Blocks(Describe.Lean(
            DescribeId.Create("single-context-visible-remainder-dimension"),
            DeclarationHandle.Create(Declaration),
            H("A single context exposes exactly its diagonal share"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let d be at least two and let B be a complete rank-one projective "
                        + "measurement. Its visible carrier is the repository's canonical "
                        + "diagonalTraceZeroSubspace inside traceZeroHermitian d; the unread "
                        + "carrier is its real Hilbert--Schmidt orthogonal complement.")),
                Paragraph(Text(
                    "The visible finrank is at most d minus one, while the orthogonal "
                        + "remainder finrank is d squared minus d. Dividing each by the "
                        + "canonical trace-zero Hermitian finrank gives both displayed forms "
                        + "of the visible and remainder ratios.")),
                Paragraph(Text(
                    "The last clause uses the range of contextProbabilityDirection, the "
                        + "actual real-linear probability-vector readout on trace-zero state "
                        + "directions. Its ratio is one over d plus one. This is a ratio of "
                        + "linear dimensions, not probability mass of an individual state."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula basis = F.Id("B");
        Formula diagonal = Call("diagonalTraceZeroSubspace", basis);
        Formula orthogonal = Call("orthogonal", diagonal);
        Formula visible = Call("visibleRatio", basis);
        Formula remainder = Call("remainderRatio", basis);
        Formula exposed = Call("probabilityVectorExposedRatio", basis);
        Formula dMinusOne = Seq(d, Sp, Minus, Sp, D(1));
        Formula dSquared = new Formula.Power(d, D(2));
        Formula dSquaredMinusOne = Seq(dSquared, Sp, Minus, Sp, D(1));
        Formula dSquaredMinusD = Seq(dSquared, Sp, Minus, Sp, d);
        Formula dPlusOne = Seq(d, Sp, Plus, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", d), Comma, Sp,
            d, Sp, Geq, Sp, D(2), Sp, Land, Sp,
            Call("IsRecordMeasurement", Call("projector", basis)),
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Call("finrankR", diagonal), Sp, Le, Sp, dMinusOne,
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", orthogonal), Sp, Eq, Sp, dSquaredMinusD,
            Sp, Land, RowBreak, Grp(),
            visible, Sp, Eq, Sp, Frac, Grp(dMinusOne), Grp(dSquaredMinusOne),
            Sp, Land, RowBreak, Grp(),
            visible, Sp, Eq, Sp, Frac, Grp(D(1)), Grp(dPlusOne),
            Sp, Land, RowBreak, Grp(),
            remainder, Sp, Eq, Sp, Frac, Grp(dSquaredMinusD), Grp(dSquaredMinusOne),
            Sp, Land, RowBreak, Grp(),
            remainder, Sp, Eq, Sp, Frac, Grp(d), Grp(dPlusOne),
            Sp, Land, RowBreak, Grp(),
            exposed, Sp, Eq, Sp, Frac, Grp(D(1)), Grp(dPlusOne), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
