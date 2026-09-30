using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinHTransversalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/LatinHTransversals.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ghafari2026transversals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every transversal of the literal H-family square contains at least two of its three distinguished entries.",
        H("The distinguished-entry obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("latin-h-transversal-obstruction"),
                DeclarationHandle.Create(Prefix + "transversal_obstruction"),
                H("The distinguished-entry obstruction"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The square adds its priority increment to the row and column representatives modulo four k. The three literal profiles use affine cap columns and four bulk progressions, with the cap choice depending on the parity of k. Choosing the unique entry in each row of an arbitrary transversal gives column and symbol permutations. Their sums force the total priority increment to be congruent to two k modulo four k. The row lower bounds sum to minus two k plus three. If at most one distinguished entry is selected, the upper bound is two k minus three, which contradicts that congruence."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Rows(Formula k) => Call("Fin", Call("order", k));
    private static Formula Entries(Formula k) => Call("Prod", Rows(k), Call("Prod", Rows(k), Rows(k)));

    private static Formula ObstructionFormula()
    {
        var k = F.Id("k"); var s = F.Id("S");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("S", Call("Set", Entries(k)), Imp(Call("IsTransversal", k, s),
                Le(D(2), Call("ncard", Call("inter", Call("D", k), s))))))));
    }
}
