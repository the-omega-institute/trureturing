using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class OffLineZeroNegativeWeilSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stored nontriviality of every ZeroData zero discharges nonreality and yields "
            + "the final full and finite-cutoff off-line Weil-square separators.",
        H("Off-Line Zero Negative Weil Square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-data-im-ne-zero"),
                DeclarationHandle.Create(Prefix + "zeroData_im_ne_zero"),
                H("Stored nontrivial zeros have nonzero imaginary part"),
                StatementSource.FromAuthor(NonrealFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ZeroData.zero_isNontrivial supplies the stored zero's nontriviality. "
                        + "The frozen alternating-zeta nonreality theorem then rules out a "
                        + "zero imaginary part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-zero-negative-weil-square"),
                DeclarationHandle.Create(
                    Prefix + "offLineZero_yields_negative_weil_square"),
                H("An off-line stored zero yields a negative full Weil-square zero sum"),
                StatementSource.FromAuthor(FullSeparatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The addressable nonreality theorem discharges hIm in the frozen "
                            + "off-line nonreal separator. Thus every stored off-line "
                            + "nontrivial zero gives a Weil test function whose convolution "
                            + "square has strictly negative full zero-sum real part.")),
                    Paragraph(Text(
                        "This final separator does not prove that O-6 implies the Riemann "
                            + "hypothesis and does not assert that ZeroData is inhabited; "
                            + "the M1-b inhabitance obligation remains open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-zero-negative-truncated-weil-square"),
                DeclarationHandle.Create(
                    Prefix + "offLineZero_negative_truncated_weil_square"),
                H("An off-line stored zero in a cutoff yields a negative truncated Weil square"),
                StatementSource.FromAuthor(TruncatedSeparatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an index in the symmetric cutoff, the same addressable nonreality "
                        + "theorem discharges hIm in the frozen finite-cutoff separator. "
                        + "The conclusion concerns only the truncated zero sum."))),
                DescribeRole.Theorem)),
        []));

    private static Formula NonrealFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula zero = Call("zero", zeroData, index);

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("n", Naturals())],
            NotEqual(ImaginaryPart(zero), D(0))));
    }

    private static Formula FullSeparatorFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula test = F.Id("g");
        Formula witness = F.Id("hZero");
        Formula zero = Call("zero", zeroData, index);
        Formula square = Call("convolutionSquare", test);
        Formula conclusion = Exists(
            [
                Bound("g", F.Id("WeilTestFunction")),
                Bound("hZero", Call("SymmetricConvergent", zeroData, square)),
            ],
            LessThan(
                RealPart(Call("zeroSum", zeroData, square, witness)),
                D(0)));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("n", Naturals())],
            Implies(
                NotEqual(RealPart(zero), F.Id("criticalAbscissa")),
                conclusion)));
    }

    private static Formula TruncatedSeparatorFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula cutoff = F.Id("T");
        Formula test = F.Id("g");
        Formula zero = Call("zero", zeroData, index);
        Formula square = Call("convolutionSquare", test);
        Formula premises = And(
            Member(index, Call("symmetricIndices", zeroData, cutoff)),
            NotEqual(RealPart(zero), F.Id("criticalAbscissa")));
        Formula conclusion = Exists(
            [Bound("g", F.Id("WeilTestFunction"))],
            LessThan(
                RealPart(Call(
                    "truncatedZeroSum", zeroData, square, cutoff)),
                D(0)));

        return Disp(ForAll(
            [
                Bound("Z", F.Id("ZeroData")),
                Bound("n", Naturals()),
                Bound("T", Reals()),
            ],
            Implies(premises, conclusion)));
    }

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Sp, Open, value, Close);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }

        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
