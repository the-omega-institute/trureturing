using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.SternBrocot;

internal sealed class AdamsonSternFareyInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stern's diatomic values invert the next Farey-tree numerator modulo its denominator.",
        H("Adamson's Stern-Farey Inverse Relation"),
        Blocks(
            Paragraph(Text(
                "All indices n, m, j and r are natural numbers; a and b are pairs of natural "
                    + "numerator and denominator coordinates, with subscripts 1 and 2 denoting "
                    + "their projections. The function stern is Stern's diatomic sequence, "
                    + "mediant adds both coordinates, and fareyRow(m,j) is position j in the "
                    + "full mediant row m, whose valid positions are 0 through 2^m. The "
                    + "total definition below also specifies values outside these positions. "
                    + "The pair fareyEntry(r) has numerator fareyNum(r) and denominator "
                    + "fareyDen(r). Entries 0 and 1 are 0/1 and 1/1; subsequent entries list "
                    + "each level's new mediants in increasing order in [0,1]. At "
                    + "r = 2^m + j with 1 <= j <= 2^m, the selected position is "
                    + "fareyRow(m+1,2(j-1)+1). The operator log_2 is the natural floor "
                    + "logarithm, with log_2(0)=0; / is natural-number division, subtraction "
                    + "is truncated at zero, and mod is the natural remainder. Only Adamson's "
                    + "inverse sentence is settled here; Yurramendi's frequency conjecture, "
                    + "Torres's conjectures and other Farey-tree properties are not claimed.")),
            Describe.Lean(
                DescribeId.Create("a002487-stern"),
                DeclarationHandle.Create(Prefix + "stern"),
                H("Stern's diatomic sequence"),
                StatementSource.FromAuthor(SternFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/adamson2023a002487")),
                Blocks(Paragraph(Text(
                    "The initial values are 0 and 1. At a larger even index the value "
                        + "is copied from half the index; at an odd index the two "
                        + "neighboring values at half the index are added."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-mediant"),
                DeclarationHandle.Create(Prefix + "mediant"),
                H("The mediant of two coordinate pairs"),
                StatementSource.FromAuthor(MediantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mediant adds the numerators and adds the denominators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-farey-row"),
                DeclarationHandle.Create(Prefix + "fareyRow"),
                H("Full mediant rows"),
                StatementSource.FromAuthor(FareyRowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The initial row has endpoints (0,1) and (1,1). Refinement copies "
                        + "the old entries into even positions and inserts the mediant "
                        + "of adjacent entries into each intervening odd position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-farey-entry"),
                DeclarationHandle.Create(Prefix + "fareyEntry"),
                H("The level-by-level entry selector"),
                StatementSource.FromAuthor(FareyEntryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After the two endpoints, each block consists of the new mediants "
                        + "from one refinement. The floor logarithm locates the block, "
                        + "and the odd row position locates its mediant."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-farey-num"),
                DeclarationHandle.Create(Prefix + "fareyNum"),
                H("Farey-tree numerators"),
                StatementSource.FromAuthor(ProjectionFormula("fareyNum", 1)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/adamson2023a002487")),
                Blocks(Paragraph(Text(
                    "The first coordinate gives the A007305 numerator at the same index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-farey-den"),
                DeclarationHandle.Create(Prefix + "fareyDen"),
                H("Farey-tree denominators"),
                StatementSource.FromAuthor(ProjectionFormula("fareyDen", 2)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/adamson2023a002487")),
                Blocks(Paragraph(Text(
                    "The second coordinate gives the A007306 denominator at the same index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002487-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Adamson's modular inverse relation"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/adamson2023a002487")),
                Blocks(Paragraph(Text(
                    "The coordinates of each mediant row are Stern values. The "
                        + "adjacent-column determinant identity then writes the product "
                        + "of stern(n) and fareyNum(n+1) as a multiple of fareyDen(n+1) "
                        + "plus one. Taking remainders proves the relation for every "
                        + "positive n; for example, stern(12)=2 and entry 13 is (4,7)."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a002487-adamson-stern-farey-inverse"),
                    ResolutionKind.Proved)))));

    private static Formula SternFormula()
    {
        var n = F.Id("n");
        var half = Divide(n, D(2));
        return Disp(Universal("n", Equal(Call("stern", n), Cases(
            CaseRow(D(0), Equal(n, D(0))),
            CaseRow(D(1), Equal(n, D(1))),
            CaseRow(Call("stern", half), And(
                Parenthesized(Less(D(1), n)),
                Parenthesized(Equal(Modulo(n, D(2)), D(0))))),
            CaseRow(Add(Call("stern", half), Call("stern", Add(half, D(1)))), And(
                Parenthesized(Less(D(1), n)),
                Parenthesized(NotEqual(Modulo(n, D(2)), D(0)))))))));
    }

    private static Formula MediantFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var pairs = Seq(Naturals(), Sp, Times, Sp, Naturals());
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), pairs),
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), pairs),
            ],
            Equal(Call("mediant", a, b), Pair(
                Add(Coordinate(a, 1), Coordinate(b, 1)),
                Add(Coordinate(a, 2), Coordinate(b, 2))))));
    }

    private static Formula FareyRowFormula()
    {
        var m = F.Id("m");
        var j = F.Id("j");
        var half = Divide(j, D(2));
        return Disp(new Formula.Aligned([
            Universal("j", Equal(Call("fareyRow", D(0), j), Cases(
                CaseRow(Pair(D(0), D(1)), Equal(j, D(0))),
                CaseRow(Pair(D(1), D(1)), NotEqual(j, D(0)))))),
            Universal("m", Universal("j", Equal(Call("fareyRow", Add(m, D(1)), j), Cases(
                CaseRow(Call("fareyRow", m, half), Equal(Modulo(j, D(2)), D(0))),
                CaseRow(Call("mediant",
                    Call("fareyRow", m, half),
                    Call("fareyRow", m, Add(half, D(1)))),
                    NotEqual(Modulo(j, D(2)), D(0))))))),
        ]));
    }

    private static Formula FareyEntryFormula()
    {
        var r = F.Id("r");
        var m = new Formula.Apply(
            new Formula.Subscript(Operator("log"), D(2)),
            [Subtract(r, D(1))]);
        var k = Subtract(Parenthesized(Subtract(r, D(1))), new Formula.Power(D(2), m));
        return Disp(Universal("r", Equal(Call("fareyEntry", r), Cases(
            CaseRow(Pair(D(0), D(1)), Equal(r, D(0))),
            CaseRow(Pair(D(1), D(1)), Equal(r, D(1))),
            CaseRow(Call("fareyRow", Add(m, D(1)),
                Add(Multiply(D(2), Parenthesized(k)), D(1))), Less(D(1), r))))));
    }

    private static Formula ProjectionFormula(string name, byte coordinate)
    {
        var r = F.Id("r");
        return Disp(Universal("r", Equal(Call(name, r),
            Coordinate(Parenthesized(Call("fareyEntry", r)), coordinate))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var next = Add(n, D(1));
        var denominator = Call("fareyDen", next);
        return Disp(Universal("n", Implies(
            Parenthesized(Less(D(0), n)),
            Parenthesized(Equal(
                Modulo(Multiply(Call("stern", n), Call("fareyNum", next)), denominator),
                Modulo(D(1), denominator))))));
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Operator(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Pair(Formula first, Formula second) =>
        Parenthesized(Seq(first, Comma, Sp, second));

    private static Formula Coordinate(Formula pair, byte coordinate) =>
        new Formula.Subscript(pair, D(coordinate));

    private static Formula Divide(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Slash, Sp, right));

    private static Formula Modulo(Formula value, Formula modulus) =>
        new Formula.Modulo(value, modulus);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula CaseRow(Formula value, Formula condition) =>
        Seq(value, Sp, Amp, Sp, condition);

    private static Formula Cases(params Formula[] rows)
    {
        var items = new System.Collections.Generic.List<Formula>
        {
            Begin, Grp(F.Id("cases")),
        };
        for (var index = 0; index < rows.Length; index++)
        {
            if (index > 0)
                items.Add(new Formula.LatexMacro(FormulaLatexMacro.RowBreak));
            items.Add(rows[index]);
        }
        items.Add(End);
        items.Add(Grp(F.Id("cases")));
        return Seq([.. items]);
    }
}
