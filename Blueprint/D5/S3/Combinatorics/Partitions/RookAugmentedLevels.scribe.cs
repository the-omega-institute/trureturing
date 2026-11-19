using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookAugmentedLevelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookAugmentedLevels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual augmented completions prove native factorization, exact root multiplicities, and singleton level data for arbitrary Ferrers input.",
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
                H("Same-board polynomial factorization"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/barrese2015bijections")),
                Blocks(Paragraph(Text("rookPolynomial(m,N,B) is the sum of C(rookCount(m,B,k) m^(N-k)) times the descending Pochhammer polynomial of degree N-k. levelPolynomial(m,N,B) is the product of C(columnLevel(m,B,N-1-i)) + C(m) X - C(mi). This is Barrese, Loehr, Remmel and Sagan, arXiv:1508.05944v1 §6.1, Theorem 26 at x=mt. The source takes N at least the width and the number of nonempty levels. For positive m the Lean identity uses the stronger common bound N at least area(B)+1. Its proof counts the same selections through the native Lean bijections completionEquiv and nativePartialEquiv. Both evaluations count the same augmented selections at every integer t=N+n. At those values each natural subtraction is justified by mi at most mt, so casting preserves each product factor. Polynomial.eq_of_infinite_eval_eq gives the identity on the same original board."))), DescribeRole.Theorem),
            Definition("Partial", "Actual original choices at fixed levels",
                "A Partial is an option-valued function on Fin(N). A present value retains the actual source column and within-level row, satisfies the source-height inequality, and uses a column at most once across levels."),
            Definition("Vacant", "The exact complement of occupied levels",
                "Vacant(p) is the subtype of levels where the partial function is none. Its cardinality is N minus the actual native subset cardinality."),
            Definition("completionEquiv", "Reversible auxiliary completion",
                "The dependent sum of Partial p, an embedding Vacant(p) into Fin(t), and a function Vacant(p) into Fin(m) is equivalent to the exact Selections type on the augmented levels. Both composites are identities."),
            Definition("nativeCoord", "Native coordinates with reflection",
                "A level i and source cell (c,r) map to the literal pair (m(N-1-i)+r,c.rev). Positive m makes this coordinate map injective; the area-based common length makes it cover every source cell."),
            Definition("NativePlacements", "Unstratified native subsets",
                "This is the subtype of the powerset of the genuine cells(B) satisfying the exact Nonattacking(m) predicate, before a subset size is selected."),
            Definition("nativePartialEquiv", "Reversible transport to genuine subsets",
                "For positive m and N at least area(B)+1, nativePartialEquiv identifies Partial with NativePlacements. It proves membership, nonattacking legality and both inverse laws on the actual cell coordinates."),
            Definition("rookPolynomial", "Native falling-factorial expansion",
                "Sum over k from zero through N of C(rookCount(m,B,k) m^(N-k)) times descPochhammer over the integers of degree N-k."),
            Definition("levelPolynomial", "Same-board level product",
                "Product over i in Fin(N) of C(columnLevel(m,B,N-1-i)) + C(m) X - C(mi). Integer subtraction has no truncation."),
            Definition("levelRoots", "Actual level roots",
                "The integer at i is mi minus columnLevel(m,B,N-1-i). RookClassCandidate identifies this exact function with the registered seedRoots at every registered common length."),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-polynomial-equivalence"), DeclarationHandle.Create(Prefix + "rookEquivalent_iff_levelPolynomial"),
                H("Native equivalence and equality of level products"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive m and a common N at least area(A)+1 and area(B)+1, RookEquivalent(m,A,B) holds exactly when their levelPolynomials agree. Descending Pochhammer polynomials form a polynomial sequence with distinct degrees. Linear independence recovers each rook coefficient through N, and the positive factor m^(N-k) cancels. Counts above N vanish by the actual area bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-root-multiplicities"), DeclarationHandle.Create(Prefix + "levelPolynomial_eq_iff_roots"),
                H("Exact root multiplicities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive m, every N and arbitrary normalized A,B, equality of levelPolynomials is equivalent to permutation equality of their complete levelRoots lists. Substitution by mX is injective, as shown by infinitely many distinct integer multiples of m. Roots of the product of X minus each root recover the full multiset, preserving repeated entries."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-singleton-image"), DeclarationHandle.Create(Prefix + "level_totals_singleton"),
                H("The actual level tuple is singleton"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive m, any N and arbitrary normalized B, the top-down level-total function is SingletonColumns. The original B need not be singleton. If an upper level occupies c columns, its cardinality is at most mc, while every lower level contains all mc cells of those columns. A nonmultiple upper total is strictly below mc, forcing a strict increase of quotient before another partial total can have that quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rookaugmentedlevels-total-area"), DeclarationHandle.Create(Prefix + "level_totals_sum"),
                H("Level totals preserve the actual area"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive m and every N at least area(B)+1, the sum over all N top-down columnLevel totals is area(B). An explicit finite bijection maps every valid level, source column and row triple to the genuine cells(B); row division and remainder and the reflected source column give its inverse."))), DescribeRole.Theorem),
            Paragraph(Text("These are symbolic results for arbitrary boards, including the empty board. They supply the native class identification in RookClassCandidate. The exact registered UniversalFormula and weight Q are unchanged. The proofs reuse the pinned Mathlib embedding cardinality, descending Pochhammer sequence and root-product identities. In arXiv:1508.05944v1, §6.1 gives the factorization and §6.2 asks for the whole-class count. The admissibility test for singleton root vectors is Proposition 4.4 of arXiv:1308.4081v1."))
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
