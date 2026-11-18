using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookRootIndexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookRootIndex.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct root sequences reconstruct normalized singleton boards with a finite multinomial bound.",
        H("Finite root indices and unique normalized reconstruction"), Blocks(
            Definition("heights", "Integer heights", "At position i, heights(m,a,i)=mi-a(i) in the integers."),
            Definition("Admissible", "The exact admissibility filter",
                "Require a(i)=0 at the first position, nonnegative heights, weakly increasing heights, and the original conditional RootFloorCriterion. When the length is positive, the first-position clause is a(0)=0. The empty tuple is also defined, although all registered common lengths are positive."),
            Definition("rootPermutations", "Distinct multiset sequences",
                "List all permutations of the finite root list, deduplicate the lists as a Finset, and convert them back to fixed-length functions. Membership is equivalent to List.Perm of the root lists, hence equality of their integer multisets. Equal root entries receive no labels and create no extra indices."),
            Definition("indices", "The finite source index", "Filter rootPermutations by Admissible. No original board-class search occurs in this definition."),
            Definition("decode", "Natural padded columns", "Take the natural conversion of each integer height. Admissibility proves it is nonnegative, so conversion preserves the entire integer value."),
            Definition("board", "The normalized representative",
                "Form the decoded weakly increasing column list and remove its zero prefix. The implementation filters zero entries; sortedness proves these entries form exactly a prefix. No positive column is removed or reordered. The empty positive-column list remains allowed."),
            Definition("paddedRoots", "Roots of the same reconstructed board", "Prepend zero columns to length N and subtract each resulting height from mi. The default-zero accessor makes the definition total; the reconstruction theorem proves the padded list has exactly the required length."),
            Theorem("board_injective", "Fixed-length representatives are distinct", Injective(),
                "Re-padding each reconstructed board recovers every decoded height, hence every original root. Equal normalized boards therefore give equal root sequences, including repeated roots and all-zero decoded tuples."),
            Theorem("reconstruction", "Exact padding and geometric singleton law", Reconstruction(false),
                "At every positive m and every finite root seed z, each admissible index re-pads to its full decoded tuple, recovers its entire original root sequence, and satisfies the geometric singleton condition. This does not assert native rook equivalence to an input board."),
            Definition("multiplicityFactor", "Root multiplicity factorials",
                "Multiply the factorial of each value's multiplicity over the distinct values of the root tuple. The empty product is one. A multiplicity counts positions with that value, without labeling the equal values."),
            Theorem("index_family", "The simultaneous finite index specification", Family(),
                "For any natural seed columns d, every admissible permutation reconstructs a board of exactly the sum of d. The same family has distinct normalized representatives, satisfies the exact padding and geometric singleton properties, and has cardinality at most N! divided by the product of the root multiplicity factorials. The bound reuses Mathlib's orbit-stabilizer theorem and DomMulAct.stabilizer_card', identifying the orbit with root-multiset sequences. Sum equality of roots proves area equality for the same reconstructed board. There is no singleton, positivity or sortedness restriction on the seed d; only the reconstructed columns are filtered. The unproved interface is whether the native rook class maps exactly onto this root family.")
        ), []));
    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rookrootindex-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rookrootindex-" + declaration.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, Seq(Open, y, Close));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Nat() => I("Nat");
    private static Formula Tuple(Formula type) => new Formula.TypeArrow(Call("Fin", I("n")), type);
    private static Formula Roots() => Call("root", I("m"), I("d"));
    private static Formula Index(Formula z) => Call("indices", I("m"), z);
    private static Formula Board() => Call("board", I("m"), I("a"));
    private static Formula Details() => And(Eq(Call("pad", I("n"), Board()), Call("ofFn", Call("decode", I("m"), I("a")))),
        And(Eq(Call("paddedRoots", I("m"), I("n"), Board()), I("a")), Call("SingletonColumns", I("m"), Call("decode", I("m"), I("a")))));
    private static Formula Injective() => All("m", Nat(), All("n", Nat(), All("z", Tuple(new Formula.Integers()),
        Call("Injective", Call("boardMap", I("m"), I("z"))))));
    private static Formula Reconstruction(bool unused) => All("m", Nat(), Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, I("m")),
        All("n", Nat(), All("z", Tuple(new Formula.Integers()), All("a", Call("Member", Index(I("z"))), Details())))));
    private static Formula Family() => All("m", Nat(), Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, I("m")),
        All("n", Nat(), All("d", Tuple(Nat()), And(new Formula.Relation(Call("card", Index(Roots())), FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(Call("factorial", I("n")), Call("multiplicityFactor", Roots()))),
            And(Call("Injective", Call("boardMap", I("m"), Roots())), All("a", Call("Member", Index(Roots())),
                And(Eq(Call("pad", I("n"), Board()), Call("ofFn", Call("decode", I("m"), I("a")))),
                    And(Eq(Call("paddedRoots", I("m"), I("n"), Board()), I("a")),
                        And(Call("SingletonColumns", I("m"), Call("decode", I("m"), I("a"))),
                            Eq(Call("area", Board()), Call("sum", I("d")))))))))))));
}
