using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class BooleanNullBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.";
    private static readonly LibraryNoteRef Schaefer =
        LibraryNoteRef.Create("D5/L/Computability/schaefer1978satisfiability");
    private static readonly LibraryNoteRef Sheffer =
        LibraryNoteRef.Create("D5/L/Computability/sheffer1913postulates");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting the null tuple changes whether ternary disjunction is pp definable.",
        H("The null tuple and Boolean constraint expressibility"),
        Blocks(
            Rel("five-mode-relation", "The five-mode relation", "A", 3,
                And(Equal(Call("and", At("a", 0), At("a", 2)), D(0)),
                    Equal(Call("and", At("a", 1), At("a", 2)), D(0))),
                "Bits are ordered as (x,y,z), with z the middle site. A consists exactly of "
                    + "000, 100, 001, 010 and 110. Bool false and true are written 0 and 1."),
            Rel("null-free-relation", "The null-free relation", "N", 3,
                And(Call("A", Id("a")), Neg(And(Equal(At("a", 0), D(0)),
                    And(Equal(At("a", 1), D(0)), Equal(At("a", 2), D(0)))))),
                "N removes exactly 000 from A. Equivalently its third bit is NOR of its first "
                    + "two bits: z = not(x or y). This equivalence is checked in the proof of "
                    + "the construction below."),
            Node("nor-truth-table", "The null-free relation computes NOR", "n_iff_nor",
                NorFormula(),
                "For all Boolean x, y and z, N on the ordered triple (x,y,z) holds exactly "
                    + "when z is the negation of x or y. The four satisfying triples are "
                    + "100, 010, 110 and 001.", DescribeRole.Theorem, Sheffer),
            Rel("equality", "Equality", "EQ", 2, Equal(At("a", 0), At("a", 1)),
                "The binary equality relation."),
            Rel("disequality", "Disequality", "NEQ", 2,
                new Formula.Relation(At("a", 0), FormulaRelationOperator.NotEqual, At("a", 1)),
                "The binary disequality relation."),
            Rel("zero", "The zero singleton", "C0", 1, Equal(At("a", 0), D(0)),
                "The unary relation containing only false."),
            Rel("one", "The one singleton", "C1", 1, Equal(At("a", 0), D(1)),
                "The unary relation containing only true."),
            Rel("ternary-disjunction", "Ternary disjunction", "OR3", 3,
                Equal(Call("or", Call("or", At("a", 0), At("a", 1)), At("a", 2)), D(1)),
                "OR3 contains every three-bit tuple except 000."),
            Node("majority-operation", "The ternary majority operation", "majority",
                Disp(All("a", Tuple(3), Equal(Call("majority", Id("a")),
                    Call("or", Call("or", Call("and", At("a", 0), At("a", 1)),
                        Call("and", At("a", 0), At("a", 2))),
                        Call("and", At("a", 1), At("a", 2)))))),
                "Majority preserves A, equality, disequality and both singleton constants. "
                    + "It sends the three unit vectors 100, 010, 001 to 000, so it does not "
                    + "preserve OR3. The general pp preservation theorem transfers this "
                    + "obstruction to every finite conjunction with any number of hidden variables.",
                DescribeRole.Definition, Schaefer),
            Node("native-window-coordinates", "Correspondence with native windows", "a_window_iff",
                Disp(All("x", Bool(), All("y", Bool(), All("z", Bool(),
                    Iff(Call("A", Call("tuple", Id("x"), Id("y"), Id("z"))),
                        Exists("w", Named("Window"), Equal(Call("bits", Id("w")),
                            Call("word", Id("x"), Id("z"), Id("y"))))))))),
                "Window and bits are the existing LiteralWindowEnd definitions. Native bits "
                    + "are ordered low, middle, high, so the word is [x,z,y]. The native modes "
                    + "zero, low, middle, high, ends correspond respectively to the event tuples "
                    + "000, 100, 001, 010, 110. The equivalence includes existence of a native "
                    + "window for each allowed tuple and excludes all three forbidden tuples.",
                DescribeRole.Theorem, null),
            Node("nor-atom-list", "A five-atom NOR definition", "norAtoms",
                Disp(Equal(Call("norAtoms"), Call("atoms",
                    Call("N", D(0), D(1), D(3)), Call("N", D(3), D(3), D(4)),
                    Call("N", D(4), D(2), D(5)), Call("N", D(5), D(5), D(6)),
                    Call("N", D(7), D(6), D(7))))),
                "Indices 0,1,2 denote free variables x,y,z; 3,4,5,6,7 denote hidden variables "
                    + "t,u,v,w,r. Thus the conjunction is N(x,y,t), N(t,t,u), N(u,z,v), "
                    + "N(v,v,w), N(r,w,r). The language has the single symbol N of arity three, "
                    + "represented by Unit with nArity constantly three and nRelations constantly N. "
                    + "There are no equality or constant atoms. If x or y or z holds, a hidden "
                    + "assignment is t = not(x or y), u = x or y, v = not(x or y or z), "
                    + "w = x or y or z, r = 0. Conversely the first four atoms compute w as "
                    + "the disjunction; the last atom forces w = 1.",
                DescribeRole.Definition, Sheffer),
            Node("null-tuple-boundary", "The two pp closures are separated", "result",
                ResultFormula(),
                "The first conjunct quantifies over every natural m and every atom list in "
                    + "the language with the five symbols A, EQ, NEQ, C0 and C1 and their "
                    + "respective arities 3,2,2,1,1. It rules out pointwise equivalence with OR3. "
                    + "The second conjunct supplies m = 5 and the displayed N-only list, and "
                    + "proves equivalence for every free tuple. An atom can use any variable "
                    + "index in Fin(3+m), with repetition allowed. Defines has exactly the "
                    + "finite existential-conjunction semantics above. The negative result "
                    + "uses the general polymorphism preservation theorem on its proof path. "
                    + "These conclusions concern relation expressibility. They make no assertion "
                    + "about arbitrary probability laws, proof certificates or P versus NP. "
                    + "Majority closure and NOR completeness are classical Boolean constraint "
                    + "theory; the explicit small construction identifies the effect of the null tuple.",
                DescribeRole.Theorem, Schaefer)), []));

    private static Formula NorFormula()
    {
        Formula body = Iff(Call("N", Id("x"), Id("y"), Id("z")),
            Equal(Id("z"), Call("not", Call("or", Id("x"), Id("y")))));
        return Disp(All("x", Bool(), All("y", Bool(), All("z", Bool(), body))));
    }

    private static Formula ResultFormula()
    {
        Formula m = Id("m"), l = Id("L"), a = Id("a");
        Formula baseAtoms = Call("List", Call("Atom", Named("baseArity"), Add(D(3), m)));
        Formula nAtoms = Call("List", Call("Atom", Named("nArity"), Add(D(3), m)));
        Formula negative = All("m", Nat(), All("L", baseAtoms,
            Neg(All("a", Tuple(3), Iff(Call("Defines", Named("baseRelations"), l, a),
                Call("OR3", a))))));
        Formula positive = Exists("m", Nat(), Exists("L", nAtoms,
            All("a", Tuple(3), Iff(Call("Defines", Named("nRelations"), l, a),
                Call("OR3", a)))));
        return Disp(And(negative, positive));
    }

    private static DocumentBlock Rel(string id, string title, string name, byte arity,
        Formula body, string prose) => Node(id, title, name,
            Disp(All("a", Tuple(arity), Iff(Call(name, Id("a")), body))),
            prose, DescribeRole.Definition, Schaefer);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, LibraryNoteRef? source) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), source is null
                ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Id(string x) => F.Id(x);
    private static Formula Named(string x) => new Formula.NamedConstant(FormulaIdentifier.Create(x));
    private static Formula Bool() => Named("Bool");
    private static Formula Nat() => Named("Nat");
    private static Formula Tuple(byte n) => Seq(Call("Fin", D(n)), Sp, To, Sp, Bool());
    private static Formula At(string x, byte n) => Call(x, D(n));
    private static Formula All(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Exists(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Group(a), FormulaLogicOperator.Iff, Group(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Group(a), FormulaLogicOperator.And, Group(b));
    private static Formula Group(Formula a) => Seq(Open, a, Close);
    private static Formula Neg(Formula a) => new Formula.Not(Group(a));
}
