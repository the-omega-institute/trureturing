using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.LatinSquares;

internal sealed class SudoQMinimumCluesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/LatinSquares/SudoQMinimumClues.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/paczosetal2021sudoq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No uniquely solvable four by four SudoQ has at most three clues.",
        H("Four clues are necessary for unique SudoQ solvability"),
        Blocks(
            Describe.Lean(DescribeId.Create("sudoq-minimum-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The three-clue conjecture"),
                StatementSource.FromAuthor(Disp(Eqn(F.Id("claim"), ClaimFormula()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section III.A, page 4: “Similarly to the classical Sudoku "
                    + "there are no 4×4 SudoQ with 3 clues that are uniquely solvable.” "
                    + "The thesis Quantum mappings and designs, Chapter 7, restates it as "
                    + "“Uniquely solvable grids of 4 × 4 SudoQ admit at least 4 clues.” "
                    + "C is the finite set of nonblank cells and v assigns their literal "
                    + "complex vectors. Coordinates start at zero. The at-most-three "
                    + "statement includes zero, one and two clues as well as three. "
                    + "Unique solvability includes existence and compares completions "
                    + "entry by entry as rays."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sudoq-minimum-result"),
                DeclarationHandle.Create(Prefix + "result"), H("At most three clues never suffice"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Suppose a solution were unique. The clue geometry "
                    + "then forces a repeated ray in every row, column and block. "
                    + "Sudoku-preserving row and column permutations put its four "
                    + "positions in a fixed pattern. Orthogonality forces one of two "
                    + "normal forms, exchanged by transposition. In either form, four "
                    + "disjoint rectangles partition the cells, and each supports a "
                    + "swap of two orthogonal rays. Three clues miss a rectangle. "
                    + "Its swap gives a second solution with a changed ray. Cells "
                    + "outside the rectangle retain their original vectors literally, "
                    + "so every prescribed clue is preserved. The argument applies "
                    + "to arbitrary clue vectors and also excludes unique solvability "
                    + "when there is no completion."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("paczos-et-al-2021-sudoq-three-clues"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinType(byte n) => Call("Fin", D(n));
    private static Formula Cells() => Seq(FinType(4), Sp, Times, Sp, FinType(4));
    private static Formula ClaimFormula() => All("C", Call("Finset", Cells()),
        All("v", new Formula.TypeArrow(Cells(), Call("EuclideanSpace", ComplexType(), FinType(4))),
            new Formula.Logic(
                new Formula.Relation(Seq(Q("Finset", "card"), Sp, F.Id("C")),
                    FormulaRelationOperator.LessThanOrEqual, D(3)),
                FormulaLogicOperator.Implies,
                new Formula.Not(Call("UniquelySolvable", F.Id("C"), F.Id("v"))))));
}
