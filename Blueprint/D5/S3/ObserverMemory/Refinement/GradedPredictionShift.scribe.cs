using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class GradedPredictionShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive finite prediction quotients carry a graded shift that closes after stabilization.",
        H("Graded Prediction Shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("graded-prediction-shift-closes-after-stabilization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/GradedPredictionShift."
                    + "graded_prediction_shift"),
                H("The graded shift closes on a stabilized quotient"),
                StatementSource.FromAuthor(ShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At depth m, states are identified when their readout words through m "
                        + "agree. Updating a representative of the depth m + 1 quotient gives "
                        + "a well-defined class at depth m, while the identity representative "
                        + "gives the forgetful projection.")),
                    Paragraph(Text(
                        "On finite words, the first map deletes the current coordinate and the "
                        + "second deletes the final coordinate. These identities make the two "
                        + "quotient maps exact encodings of the finite-word shift.")),
                    Paragraph(Text(
                        "If the depth m and depth m + 1 kernel relations agree, the repository's "
                        + "permanent-stability theorem identifies every later relation with the "
                        + "same kernel. The forgetful projection is then bijective, the stabilized "
                        + "finite quotient is equivalent to the complete-itinerary quotient, and "
                        + "the induced closed update is conjugate to the existing completion update.")),
                    Paragraph(Text(
                        "Pinned Mathlib quotient-map, quotient-congruence, kernel-range, and "
                        + "bijection constructors are applied directly. Repository and library "
                        + "searches found no result combining both maps, both word identities, "
                        + "the stage bijection, and the closed dynamics."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ClassAt(Formula value, Formula depth) =>
        Seq(OpenBracket, value, CloseBracket, Underscore, Grp(depth));

    private static Formula ShiftFormula()
    {
        Formula m = F.Id("m");
        Formula next = Seq(m, Sp, Plus, Sp, D(1));
        Formula y = F.Id("y");
        Formula shift = Subscript(F.Id("s"), m);
        Formula projection = Subscript(F.Id("p"), Seq(next, Comma, m));
        Formula wordM = Subscript(F.Id("W"), m);
        Formula wordNext = Subscript(F.Id("W"), next);
        Formula relationM = Subscript(F.Id("R"), m);
        Formula relationNext = Subscript(F.Id("R"), next);
        Formula stateM = Subscript(F.Id("Z"), m);
        Formula completeState = Subscript(F.Id("Z"), Infty);
        Formula closedUpdate = BarredSubscript(Tau, m);
        Formula completionUpdate = BarredSubscript(Tau, Infty);
        Formula equivalence = Subscript(F.Id("e"), m);

        return Disp(Seq(
            Forall, Sp, m, Comma, Sp, y, Comma, Esc,
            Apply(shift, ClassAt(y, next)), Sp, Eq, Sp,
            ClassAt(Apply(Tau, y), m), Sp, Land, Esc,
            Apply(projection, ClassAt(y, next)), Sp, Eq, Sp,
            ClassAt(y, m), Sp, Land, Esc,
            Call("deleteCurrent", Apply(wordNext, y)), Sp, Eq, Sp,
            Apply(wordM, Apply(Tau, y)), Sp, Land, Esc,
            Call("restrictFinal", Apply(wordNext, y)), Sp, Eq, Sp,
            Apply(wordM, y), Sp, Land, Esc,
            Open, relationM, Sp, Eq, Sp, relationNext, Sp, Rightarrow, Esc,
            Call("Bijective", projection), Sp, Land, Esc,
            stateM, Sp, Equiv, Sp, completeState, Sp, Land, Esc,
            shift, Sp, Eq, Sp, closedUpdate, Sp, Circ, Sp, projection, Sp, Land, Esc,
            equivalence, Sp, Circ, Sp, closedUpdate, Sp, Eq, Sp,
            completionUpdate, Sp, Circ, Sp, equivalence, Close, Dot));
    }

    private static Formula BarredSubscript(Formula value, Formula index) =>
        Seq(Overline, Grp(value), Underscore, Grp(index));
}
