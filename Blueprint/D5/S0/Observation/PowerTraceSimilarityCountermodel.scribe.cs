using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class PowerTraceSimilarityCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two explicit matrices have identical positive-power traces and characteristic polynomial but belong to different similarity classes.",
        H("Power Traces Do Not Determine Similarity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-traces-do-not-determine-similarity"),
                DeclarationHandle.Create(
                    "D5/S0/Observation/PowerTraceSimilarityCountermodel."
                        + "power_traces_do_not_determine_similarity"),
                H("All power traces can miss the similarity class"),
                StatementSource.FromAuthor(CountermodelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Over an arbitrary field, take A to be the two-by-two zero matrix and N "
                            + "to have its only nonzero entry, one, in row zero and column one. "
                            + "The matrix N is nonzero and square-zero.")),
                    Paragraph(Text(
                        "Every positive power of A and N has trace zero, and both characteristic "
                            + "polynomials are X squared. Their ranks are zero and one, so no "
                            + "invertible change of basis conjugates A to N. The same pair directly "
                            + "refutes the universal claim that all positive-power traces determine "
                            + "matrix similarity.")),
                    Paragraph(Text(
                        "The result is stronger than the source's characteristic-zero context: "
                            + "the countermodel works over every field. Pinned Mathlib supplies the "
                            + "two-dimensional characteristic-polynomial formula and rank bounds, "
                            + "but no theorem packages this full countermodel."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula FieldMatrices(Formula field) =>
        Call("Matrix", D(2), D(2), field);

    private static Formula PowerTrace(Formula matrix, Formula exponent) =>
        Call("tr", Seq(matrix, Caret, Grp(exponent)));

    private static Formula Charpoly(Formula matrix) =>
        Call("charpoly", matrix);

    private static Formula Rank(Formula matrix) =>
        Call("rank", matrix);

    private static Formula Conjugate(Formula basis, Formula matrix) =>
        Seq(basis, matrix, basis, Caret, Grp(Minus, D(1)));

    private static Formula CountermodelFormula()
    {
        Formula field = F.Id("K");
        Formula exponent = F.Id("k");
        Formula zeroMatrix = F.Id("A");
        Formula nilpotent = F.Id("N");
        Formula first = F.Id("M");
        Formula second = F.Id("C");
        Formula basis = F.Id("P");
        Formula matrices = FieldMatrices(field);
        Formula xSquared = new Formula.Power(F.Id("X"), D(2));

        Formula EqualPositivePowerTraces(Formula left, Formula right) => Seq(
            Forall, Sp, exponent, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(1), Sp, Le, Sp, exponent, Sp, Rightarrow, Sp,
            PowerTrace(left, exponent), Sp, Eq, Sp, PowerTrace(right, exponent));

        Formula ConjugateExists(Formula left, Formula right) => Seq(
            Exists, Sp, basis, Sp, InMacro, Sp, Call("GL", D(2), field), Colon, Sp,
            Conjugate(basis, left), Sp, Eq, Sp, right);

        return Disp(Seq(
            Forall, Sp, field, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Field", field), Sp, Rightarrow, Esc,
            zeroMatrix, Sp, Eq, Sp, Call("zeroMatrix", D(2), field),
            Comma, Sp,
            nilpotent, Sp, Eq, Sp, Call("single", D(2), D(0), D(1), D(1), field),
            Comma, Esc,
            Open,
            Forall, Sp, exponent, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(1), Sp, Le, Sp, exponent, Sp, Rightarrow, Sp,
            Open,
            PowerTrace(zeroMatrix, exponent), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            PowerTrace(nilpotent, exponent), Sp, Eq, Sp, D(0),
            Close,
            Close, Sp, Land, Esc,
            Charpoly(zeroMatrix), Sp, Eq, Sp, xSquared, Sp, Land, Esc,
            Charpoly(nilpotent), Sp, Eq, Sp, xSquared, Sp, Land, Esc,
            Rank(zeroMatrix), Sp, Eq, Sp, D(0), Sp, Land, Esc,
            Rank(nilpotent), Sp, Eq, Sp, D(1), Sp, Land, Esc,
            Neg, Sp, Open, ConjugateExists(zeroMatrix, nilpotent), Close,
            Sp, Land, Esc,
            Neg, Sp,
            Open,
            Forall, Sp, first, Comma, Sp, second, Sp, InMacro, Sp, matrices,
            Comma, Sp,
            Open, EqualPositivePowerTraces(first, second), Close,
            Sp, Rightarrow, Sp,
            ConjugateExists(first, second),
            Close, Dot));
    }
}
