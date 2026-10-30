using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class SimpleEvolutionAutomorphismMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static readonly LibraryNoteRef SimplicitySource = LibraryNoteRef.Create("D5/L/QuadraticForms/cabrera2016evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full automorphism maximum for simple complex evolution algebras.",
        H("The simple evolution algebra automorphism maximum"),
        Blocks(
            Paragraph(Text("A complex evolution algebra has a finite natural basis with zero mixed products. Its multiplication need not be associative or unital. The full automorphism group consists of all complex linear equivalences preserving multiplication on every pair of vectors.")),
            Describe.Lean(
                DescribeId.Create("simple"), DeclarationHandle.Create(Prefix + "IsSimple"), H("Simplicity"),
                StatementSource.FromAuthor(Disp(VectorContext(X("A"),
                    All(X("mu"), Product(X("A")), Eq(App(Name("IsSimple"), X("mu")), SimpleBody()))))),
                AssessedProvenance.FromLiterature(SimplicitySource),
                Blocks(Paragraph(Text("The survey's Theorem 6 uses simplicity in the usual ideal sense. Its cited Cabrera Casado, Siles Molina and Velasco source, arXiv:1601.01832v2, section 4, page 18, states: “We recall that an algebra A is simple if A² ≠ 0 and 0 is the only proper ideal.” Here A² is productSpan, and ideals are all complex vector subspaces absorbing products on both sides. They are not restricted to spans of natural-basis vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"), H("Conjecture 4"),
                StatementSource.FromAuthor(Disp(Eq(Name("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4, section 2.3, page 28: “Over ℂ, the maximal order of the automorphism group of a simple n-dimensional evolution algebra is max{n!, n(2ⁿ−1)}.” The dimension n is positive. The universal part ranges over arbitrary complex vector spaces A, finite index types I, bilinear products mu and natural bases b, with finrank equal to n. The existential part gives a product on Coord n attaining the bound. Finite is stated before Nat.card, so an infinite group cannot meet the bound by having natural cardinality zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"), H("The attained maximum"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Simplicity forces the support graph to be strongly connected. Every support path projects to an orbit of the successor permutation on the least successor-compatible quotient, so this permutation has a single orbit. Invertibility of the structure map supplies a permutation supported on the arrows. Restricting it to consecutive quotient fibers gives bijections, forcing every fiber to have the same positive size k. If the quotient has h elements, then n=hk.")),
                    Paragraph(Text("The joint bound for the actual algebra group becomes h(2ʰ−1)(k!)ʰ. For h,k at least two, an induction using ascending factorials bounds this by (hk)!. The cases h=1 and k=1 give n! and n(2ⁿ−1), respectively. The argument uses the actual kernel and permutation image of the same algebra.")),
                    Paragraph(Text("The cyclic product has full group order n(2ⁿ−1). The product with structure matrix I+J, where every entry of J is one, is simple and has full group order n!: every permutation lifts, while loops force every diagonal automorphism to be the identity. Choosing the larger family proves attainment in every positive dimension, including dimension one. The upper-bound argument also works without a separate commutativity hypothesis when the mixed products of a finite natural basis vanish."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kmvc4-simpleaut"), ResolutionKind.Proved)))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(variable, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LeqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Complex => Seq(Mathbb, Grp(X("C")));
    private static Formula Natural => Seq(Mathbb, Grp(X("N")));
    private static Formula Product(Formula carrier) => Call("LinearMap", Complex, carrier, Call("LinearMap", Complex, carrier, carrier));
    private static Formula Basis(Formula index, Formula carrier) => App(Q("Module", "Basis"), index, Complex, carrier);
    private static Formula VectorContext(Formula carrier, Formula body) => All(carrier, Name("Type"),
        Instance(Call("AddCommGroup", carrier), Instance(Call("Module", Complex, carrier), body)));
    private static Formula Mu => X("mu");
    private static Formula B => X("b");
    private static Formula N => X("n");
    private static Formula Aut => Call("Aut", Mu);
    private static Formula Card => App(Q("Nat", "card"), Aut);
    private static Formula Maximum => Call("max", App(Q("Nat", "factorial"), N),
        new Formula.Binary(N, FormulaBinaryOperator.Multiply,
            Parenthesized(new Formula.Binary(new Formula.Power(D(2), N), FormulaBinaryOperator.Subtract, D(1)))));
    private static Formula Mixed(Formula index) => All(X("i"), index, All(X("j"), index,
        Imp(Ne(X("i"), X("j")), Eq(App(Mu, App(B, X("i")), App(B, X("j"))), D(0)))));
    private static Formula SimpleBody() => And(Ne(Call("productSpan", Mu), Q("Bot", "bot")),
        All(X("J"), Call("Submodule", Complex, X("A")),
            Imp(All(X("x"), X("A"), Imp(new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf, X("J")),
                All(X("y"), X("A"), And(
                    new Formula.Relation(App(Mu, X("x"), X("y")), FormulaRelationOperator.MemberOf, X("J")),
                    new Formula.Relation(App(Mu, X("y"), X("x")), FormulaRelationOperator.MemberOf, X("J")))))),
                Or(Eq(X("J"), Q("Bot", "bot")), Eq(X("J"), Q("Top", "top"))))));
    private static Formula Universal() => VectorContext(X("A"),
        Instance(Call("FiniteDimensional", Complex, X("A")),
            All(X("I"), Name("Type"), Instance(Call("Fintype", X("I")),
                All(Mu, Product(X("A")), All(B, Basis(X("I"), X("A")),
                    Imp(Eq(App(Q("Module", "finrank"), Complex, X("A")), N),
                        Imp(Mixed(X("I")),
                            Imp(All(X("x"), X("A"), All(X("y"), X("A"),
                                Eq(App(Mu, X("x"), X("y")), App(Mu, X("y"), X("x"))))),
                                Imp(Call("IsSimple", Mu), And(Call("Finite", Aut), LeqTo(Card, Maximum))))))))))));
    private static Formula Attainment() => Some(Mu, Call("Product", N),
        And(Eq(App(Q("Module", "finrank"), Complex, Call("Coord", N)), N),
            And(Call("commutative", Mu), And(Call("hasNaturalBasis", Mu), And(Call("IsSimple", Mu),
                And(Call("Finite", Aut), Eq(Card, Maximum)))))));
    private static Formula ClaimBody() => All(N, Natural, Imp(LeqTo(D(1), N), And(Universal(), Attainment())));
}
