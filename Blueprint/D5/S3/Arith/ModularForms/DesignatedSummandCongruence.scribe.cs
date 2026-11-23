using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandCongruence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact common power of two on degrees congruent to three modulo four is determined for every positive tuple count.",
        H("Exact dyadic divisibility for designated summands"),
        Blocks(
            Paragraph(Text("The ordered marked count is the degree coefficient of the corresponding power of F. For odd k the reciprocal dissection kills the missing residue after dilating the power k+1. When four divides k, dyadic dilation kills every odd degree at the required modulus. For k congruent to two modulo four, the square dissection and divisibility of the odd coefficients of W give the remaining bounds.")),
            Describe.Lean(DescribeId.Create("designatedsummand-exceptional-sharp"),
                DeclarationHandle.Create(Prefix + "exceptional_sharp"),
                H("Degree seven in the exceptional class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural k congruent to 2 modulo 16, the degree-seven coefficient of F to the power k is 8 modulo 16. Modulo 16, F to the power 64 has constant coefficient one and zero coefficients in degrees one through seven. For every natural k, the degree-seven coefficient of F to the power k modulo 16 therefore depends only on k modulo 64. Convolution modulo 16 through degree seven gives residue 8 for each of the four classes 2, 18, 34 and 50 modulo 64."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("designatedsummand-common-dyadic-exponent"),
                DeclarationHandle.Create(Prefix + "result"), H("Common dyadic exponent"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive k, the largest power of 2 dividing all Aₖ(4n+3) is 2 to the valuation of Aₖ(3) when k is not congruent to 2 modulo 16, and exactly 2³ when k is congruent to 2 modulo 16. Degree three attains the first bound and degree seven attains the second."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k"), e = F.Id("e"), n = F.Id("n");
        var progression = new Formula.Binary(
            new Formula.Binary(F.D(4), FormulaBinaryOperator.Multiply, n),
            FormulaBinaryOperator.Add, F.D(3));
        var divisibility = new Formula.Relation(new Formula.Power(F.D(2), e),
            FormulaRelationOperator.Divides, Call("markedCount", k, progression));
        var allDegrees = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Naturals(), divisibility);
        var exceptional = new Formula.Relation(new Formula.Modulo(k, F.D(1, 6)),
            FormulaRelationOperator.Equal, F.D(2));
        var bound = F.Seq(F.Open, Keyword("if"), F.Sp, exceptional, F.Sp,
            Keyword("then"), F.Sp, F.D(3), F.Sp, Keyword("else"), F.Sp,
            Call("padicValNat", F.D(2), Call("markedCount", k, F.D(3))), F.Close);
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var equivalence = new Formula.Logic(allDegrees, FormulaLogicOperator.Iff,
            new Formula.Relation(e, FormulaRelationOperator.LessThanOrEqual, bound));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("k"), Naturals()), new(FormulaIdentifier.Create("e"), Naturals())],
            new Formula.Logic(positive, FormulaLogicOperator.Implies, equivalence)));
    }

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Keyword(string name) => F.Seq(F.Operatorname, F.Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
