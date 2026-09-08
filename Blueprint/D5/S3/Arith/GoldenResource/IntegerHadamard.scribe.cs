using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class IntegerHadamardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/IntegerHadamard.";
    private static readonly LibraryNoteRef HadamardSource =
        LibraryNoteRef.Create("D5/L/Arith/linsinnamon2020hadamard");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive definite integer matrix has a positive integer determinant bounded by its diagonal product, with equality exactly for a diagonal matrix.",
        H("Hadamard Bound for Integer Matrices"),
        Blocks(
            Paragraph(Text("Let n be a finite index type. For an integer matrix T, let R(T) denote its entrywise inclusion into the real matrices and let D(T) denote the diagonal matrix with the same diagonal entries. Positive definiteness of R(T) includes symmetry. Products are over all indices in n, with the empty product equal to one.")),
            Describe.Lean(
                DescribeId.Create("integer-positive-definite-hadamard"),
                DeclarationHandle.Create(Prefix + "integer_posDef_hadamard"),
                H("Positive integer determinant and equality condition"),
                StatementSource.FromAuthor(HadamardFormula()),
                AssessedProvenance.FromLiterature(HadamardSource),
                Blocks(Paragraph(Text("The diagonal entries are positive by positive definiteness. Their diagonal matrix is positive definite as well. The divergence between T and this diagonal matrix equals the logarithm of the diagonal product minus the logarithm of the determinant: its trace correction vanishes. Nonnegativity gives the determinant bound, and vanishing of the divergence gives precisely the diagonal equality condition. The determinant belongs to the integers because the determinant is a polynomial with integer coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nondiagonal-integer-determinant-gap"),
                DeclarationHandle.Create(Prefix + "nondiagonal_integer_det_gap"),
                H("An integer loss away from diagonal matrices"),
                StatementSource.FromAuthor(GapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nondiagonal matrix the equality condition makes the determinant bound strict. Both sides are integers, so their difference is at least one."))),
                DescribeRole.Theorem))));

    private static Formula HadamardFormula()
    {
        Formula positiveDiagonal = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("i"), F.Id("n"))],
            Relation(D(0), FormulaRelationOperator.LessThan, Entry()));
        Formula conclusion = And(positiveDiagonal,
            And(Relation(D(0), FormulaRelationOperator.LessThan, Det()),
                And(Relation(Det(), FormulaRelationOperator.LessThanOrEqual, DiagonalProduct()),
                    new Formula.Logic(
                        Relation(Det(), FormulaRelationOperator.Equal, DiagonalProduct()),
                        FormulaLogicOperator.Iff,
                        Relation(F.Id("T"), FormulaRelationOperator.Equal, Diagonal())))));
        return Quantified(new Formula.Logic(Positive(), FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula GapFormula() => Quantified(new Formula.Logic(
        And(Positive(), Relation(F.Id("T"), FormulaRelationOperator.NotEqual, Diagonal())),
        FormulaLogicOperator.Implies,
        Relation(Seq(Det(), Sp, Plus, Sp, D(1)),
            FormulaRelationOperator.LessThanOrEqual, DiagonalProduct())));

    private static Formula Quantified(Formula body) => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("Fintype", F.Id("n")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id("n")), CloseBracket, Comma, RowBreak,
        Forall, Sp, F.Id("T"), Colon, Sp,
        Call("Matrix", F.Id("n"), F.Id("n"), Seq(Mathbb, Grp(F.Id("Z")))),
        Comma, RowBreak, body,
        End, Grp(F.Id("gathered"))));

    private static Formula Positive() => Call("PosDef", Call("R", F.Id("T")));
    private static Formula Diagonal() => Call("D", F.Id("T"));
    private static Formula Det() => Call("det", F.Id("T"));
    private static Formula Entry() => Call("T", F.Id("i"), F.Id("i"));

    private static Formula DiagonalProduct() =>
        Seq(Prod, Underscore, Grp(F.Id("i"), Colon, F.Id("n")), Sp, Entry());

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
