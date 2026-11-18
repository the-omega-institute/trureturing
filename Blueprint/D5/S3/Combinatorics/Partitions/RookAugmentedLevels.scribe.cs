using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookAugmentedLevelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookAugmentedLevels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary Ferrers input with auxiliary full columns realizes the product side of level-total factorization.",
        H("Actual augmented Ferrers levels"), Blocks(
            Definition("Columns", "Disjoint source and auxiliary columns",
                "Columns(B,t) is the disjoint sum of the original positive-column positions and t auxiliary positions. Original and auxiliary columns can never be confused by their labels."),
            Definition("level", "Literal augmented cells",
                "For N levels indexed from the top, position p has bottom-up index N-1-p. An original column i contributes exactly the within-level rows r with m(N-1-p)+r below its actual source height. Every auxiliary column contributes all m within-level rows. For lengths below the board's full height, this definition counts its actual first N bottom-up levels; the registered common lengths cover the whole board."),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-count"), DeclarationHandle.Create(Prefix + "augmented_selections_count"),
                H("The level-total product on actual cells"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m,N,t and every normalized original board B, the number of full Selections of the actual augmented levels equals levelProduct(m,N,t,B). This product ranges over i in Fin(N), with factor columnLevel(m,B,N-1-i) plus mt minus mi in natural truncated subtraction. No singleton hypothesis is used. If a column contains a cell in an upper level, bottom justification gives all m cells in that column in a lower level. Auxiliary columns are full by construction. The generic selections_count theorem therefore applies, and a direct finite cell count identifies each level cardinality with columnLevel plus mt."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-native-completion"), DeclarationHandle.Create(Prefix + "native_completion_count"),
                H("Native placement and completion bijection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive m, every normalized original board B, every N at least area(B)+1, and every natural t, the same augmented selection count equals the sum for k from zero through N of rookCount(m,B,k) times m^(N-k) times the descending factorial of t of length N-k. Partial records retain precisely the original coordinates at their actual levels. completionEquiv reversibly fills their vacant levels with an embedding into the t auxiliary columns and an independent Fin(m) row function. nativePartialEquiv transports those records to literal Nonattacking cell subsets. It uses row=m(N-1-i)+r, quotient and remainder, and the source-column reflection c.rev. Its inverse recovers every original cell using the area bound; equal native levels force equal chosen cells. Stratification by the actual subset cardinality gives rookCount, and Fintype.card_embedding_eq supplies the descending factorial, including impossible-capacity cases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-native-factorization"), DeclarationHandle.Create(Prefix + "native_factorization"),
                H("Same-board polynomial factorization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rookPolynomial(m,N,B) is the sum of C(rookCount(m,B,k) m^(N-k)) times the descending Pochhammer polynomial of degree N-k. levelPolynomial(m,N,B) is the product of C(columnLevel(m,B,N-1-i)) + C(m) X - C(mi). For positive m and N at least area(B)+1 these integer polynomials are equal. Both evaluations count the same augmented selections at every integer t=N+n. At those values each natural subtraction is justified by mi at most mt, so casting preserves each product factor. Polynomial.eq_of_infinite_eval_eq gives the identity on the same original board."))), DescribeRole.Theorem),
            Paragraph(Text("The completion and factorization theorems impose no singleton condition on B and include the empty board. The remaining universal class-count obligation is to identify the native rook class with the existing root family, with all geometric and polynomial transports justified. The exact UniversalFormula and its weight Q are unchanged. Escape registration and independent pre-freeze audit remain unfinished under https://github.com/the-omega-institute/trureturing/issues/31465; these results are not frozen."))
        ), []));
    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rookaugmentedlevels-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Statement()
    {
        Formula m = I("m"), n = I("n"), t = I("t"), b = I("b"), nat = I("Nat");
        Formula equality = new Formula.Relation(Call("card", Call("Selections", m, Call("level", m, n, t, b))),
            FormulaRelationOperator.Equal, Call("levelProduct", m, n, t, b));
        return All("m", nat, All("n", nat, All("t", nat, All("b", I("PositiveColumns"), equality))));
    }
}
