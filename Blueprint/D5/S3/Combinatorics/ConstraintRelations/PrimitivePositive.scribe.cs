using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class PrimitivePositiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.";
    private static readonly LibraryNoteRef Geiger =
        LibraryNoteRef.Create("D5/L/Computability/geiger1968closed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator-preserving operations preserve primitive-positive definitions.",
        H("Primitive-positive definitions and preservation"),
        Blocks(
            Node("finite-atoms", "Finite atoms with repeated variables", "Atom",
                Disp(All("S", Type(), All("q", Fn(Id("S"), Nat()), All("n", Nat(),
                    Equal(Call("Atom", Id("q"), Id("n")),
                        Call("Sigma", Id("S"), Call("Arguments", Id("q"), Id("n")))))))),
                "A symbol s has arity q(s). An atom consists of s and a function from Fin(q(s)) "
                    + "to Fin(n). There is no injectivity condition: an argument variable may "
                    + "occur several times. Sigma here means the dependent collection of symbols "
                    + "and their argument functions. The carrier and the symbol type can be arbitrary.",
                DescribeRole.Definition),
            Node("atomic-semantics", "Interpretation of an atom", "Holds",
                Disp(All("D", Type(), All("S", Type(), All("q", Fn(Id("S"), Nat()),
                    All("n", Nat(), All("R", Call("Relations", Id("D"), Id("S"), Id("q")),
                    All("b", Call("Atom", Id("q"), Id("n")),
                    All("v", Fn(Fin(Id("n")), Id("D")),
                        Iff(Call("Holds", Id("R"), Id("b"), Id("v")),
                            Call("ApplyAtom", Id("R"), Id("b"), Id("v"))))))))))),
                "Relations assigns each symbol s a predicate on Fin(q(s)) to D. ApplyAtom "
                    + "means R(s) applied to the tuple whose ith entry is v(b.arguments(i)).",
                DescribeRole.Definition),
            Node("conjunction-semantics", "Finite conjunction", "HoldsAll",
                Disp(All("D", Type(), All("S", Type(), All("q", Fn(Id("S"), Nat()),
                    All("n", Nat(), All("R", Call("Relations", Id("D"), Id("S"), Id("q")),
                    All("L", Call("List", Call("Atom", Id("q"), Id("n"))),
                    All("v", Fn(Fin(Id("n")), Id("D")),
                        Iff(Call("HoldsAll", Id("R"), Id("L"), Id("v")),
                            Call("Conjunction", Id("R"), Id("L"), Id("v"))))))))))),
                "Conjunction is true on the empty list and is the conjunction of the head atom "
                    + "and the remaining list otherwise. Lists are finite and may contain duplicate atoms.",
                DescribeRole.Definition),
            Node("existential-semantics", "Existentially hidden variables", "Defines",
                Disp(All("D", Type(), All("S", Type(), All("q", Fn(Id("S"), Nat()),
                    All("n", Nat(), All("m", Nat(),
                    All("R", Call("Relations", Id("D"), Id("S"), Id("q")),
                    All("L", Call("List", Call("Atom", Id("q"), Add(Id("n"), Id("m")))),
                    All("a", Fn(Fin(Id("n")), Id("D")),
                        Iff(Call("Defines", Id("R"), Id("L"), Id("a")),
                            Exists("h", Fn(Fin(Id("m")), Id("D")),
                                Call("HoldsAll", Id("R"), Id("L"),
                                    Call("append", Id("a"), Id("h")))))))))))))),
                "Variables 0 through n-1 are free. The following m variables are hidden. "
                    + "Defines is the existence of one hidden assignment satisfying every atom "
                    + "under the concatenated assignment. No equality or constants are implicit; "
                    + "they must be supplied as relation symbols when desired.",
                DescribeRole.Definition),
            Node("operation-preservation", "Coordinatewise preservation", "Preserves",
                Disp(All("D", Type(), All("k", Nat(), All("n", Nat(),
                    All("f", Fn(Fn(Fin(Id("k")), Id("D")), Id("D")),
                    All("R", Fn(Fn(Fin(Id("n")), Id("D")), Prop()),
                        Iff(Call("Preserves", Id("f"), Id("R")),
                            Call("CoordinatewiseClosed", Id("f"), Id("R"))))))))),
                "For every family of k tuples in R, applying f at each coordinate yields another "
                    + "tuple in R. Both k and the relation arity n may be zero. This is preservation "
                    + "by an operation, also called a relational polymorphism.",
                DescribeRole.Definition),
            Node("pp-preservation", "Polymorphisms preserve pp definitions",
                "polymorphism_preserves_pp", PreservationFormula(),
                "For arbitrary carrier D, symbol type S, arities q, operation arity k, free "
                    + "arity n and hidden arity m, an operation preserving each generating relation "
                    + "preserves every relation defined by a finite atom list. Induction on the list "
                    + "proves preservation of its conjunction. Choose one hidden assignment for "
                    + "each input tuple and apply the same operation to those assignments. Variable "
                    + "substitution commutes with this coordinatewise operation, including repeated "
                    + "arguments. The concatenated free and hidden assignments therefore satisfy "
                    + "the entire list. This is the preservation direction of the classical "
                    + "pp/polymorphism correspondence; no converse is asserted.",
                DescribeRole.Theorem)), []));

    private static Formula PreservationFormula()
    {
        Formula d = Id("D"), s = Id("S"), q = Id("q"), k = Id("k");
        Formula n = Id("n"), m = Id("m"), r = Id("R"), f = Id("f"), l = Id("L");
        return Disp(All("D", Type(), All("S", Type(), All("q", Fn(s, Nat()),
            All("k", Nat(), All("n", Nat(), All("m", Nat(),
            All("R", Call("Relations", d, s, q), All("f", Fn(Fn(Fin(k), d), d),
            Implies(All("s", s, Call("Preserves", f, Call("R", Id("s")))),
                All("L", Call("List", Call("Atom", q, Add(n, m))),
                    Call("Preserves", f, Call("Defines", r, l)))))))))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Geiger),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Id(string x) => F.Id(x);
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula Prop() => new Formula.NamedConstant(FormulaIdentifier.Create("Prop"));
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fn(Formula a, Formula b) => Seq(Open, a, Close, Sp, To, Sp, b);
    private static Formula All(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Exists(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
