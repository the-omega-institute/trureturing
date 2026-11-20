using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CliqueFactorization;

internal sealed class AlgebraicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonedge rectangles characterize clique factorization of commutative-group-valued functions.",
        H("Algebraic clique factorization"),
        Blocks(
            Paragraph(Text("Let V be a finite vertex type, Omega a family of arbitrary coordinate state spaces, A a commutative group, G a simple graph on V, and X the dependent product of the spaces Omega(i). Updating a configuration replaces one coordinate by a specified value. Neither the individual spaces nor X need be finite or inhabited.")),
            Paragraph(Text("In the formula, X is the dependent product of Omega(k) over k : V. DependsOn(h,S) means that h(x) = h(y) whenever x and y agree on every coordinate in S. IsClique(G,S) means that every two distinct vertices of S are adjacent. The product ranges over all finite subsets of V, including the empty set.")),
            Describe.Lean(
                DescribeId.Create("algebraic-clique-factorization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CliqueFactorization/Algebraic.rectangle_iff_clique_factorization"),
                H("Rectangle identities if and only if clique factors exist"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/geigermeeksturmfels2006toric")),
                Blocks(
                    Paragraph(Text("The universes u, v and w are independent. Fintype(V) enumerates only vertices and their subsets; no finiteness condition is imposed on Omega(i). The same function f occurs in every rectangle and in reconstruction. A single factor family Phi simultaneously satisfies dependence, neutrality away from cliques, and reconstruction. Empty and singleton sets are cliques. Thus the empty factor may carry an arbitrary global constant, including when V is empty.")),
                    Paragraph(Text("If X is empty, every assertion evaluated at a configuration is vacuous and all factors may be one. Otherwise choose an internal configuration o. For S a subset of V, clamp a configuration x to o outside S. Define kappa(S,x) as f of this clamp divided by the product of kappa(T,x) over all proper subsets T of S. Recursion on finite subsets defines one total family. Its values depend only on S, and cancellation reconstructs each clamped value as the product over every subset of S.")),
                    Paragraph(Text("To show that a nonclique interaction is one, choose nonadjacent distinct vertices i and j in its support S and induct over proper subsets. Every proper subset containing both endpoints is a nonclique, so its interaction is one by induction. The remaining product is indexed by the union of the powersets of S without i and S without j. Their intersection is the powerset of S without both endpoints. The finite product union-intersection identity and the original rectangle at that doubly deleted clamp give the same product relation. Group cancellation forces kappa(S,x) to be one. This argument applies to any one family reconstructing all the anchored restrictions of the same f.")),
                    Paragraph(Text("Conversely, each clique omits at least one endpoint of a nonedge. Dependence on the clique then makes its factor satisfy the rectangle identity. Nonclique factors are one. Multiplying these identities and using reconstruction at all four configurations yields the rectangle identity for f.")),
                    Paragraph(Text("Geiger, Meek and Sturmfels, On the Toric Algebra of Graphical Models, Theorem 4.1, gives the Hammersley–Clifford equivalence for strictly positive finite discrete probability distributions. That restricted probability theorem supplies background, not the full statement here. The arbitrary-group argument above uses no normalization, order, topology, acyclicity or chordality. Factors are not asserted to be unique or supported only on maximal cliques. The theorem gives no algorithmic cost bound, probabilistic conditional-independence conclusion for arbitrary group values, or extension to semirings with zero."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Some(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Not(Formula a) => Seq(Neg, P(a));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);

    private static Formula Statement()
    {
        var v = F.Id("V"); var a = F.Id("A");
        var xspace = P(Seq(new Formula.Subscript(Prod, Seq(F.Id("k"), Colon, Sp, v)),
            Sp, Call("Omega", F.Id("k"))));
        var s = F.Id("S"); var x = F.Id("x"); var i = F.Id("i"); var j = F.Id("j");
        var subsets = Call("Finset", v);
        Formula Fun(Formula z) => Call("f", z);
        Formula Up(Formula z, Formula k, Formula value) => Call("update", z, k, value);
        Formula Phi(Formula support, Formula z) => Call("Phi", support, z);
        var rectangleEquality = Eqn(
            Mul(Fun(x), Fun(Up(Up(x, i, F.Id("a")), j, F.Id("b")))),
            Mul(Fun(Up(x, i, F.Id("a"))), Fun(Up(x, j, F.Id("b")))));
        var rectangle = All("i", v, All("j", v,
            Imp(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                Imp(Not(Call("Adj", F.Id("G"), i, j)),
                    All("x", xspace, All("a", Call("Omega", i),
                        All("b", Call("Omega", j), rectangleEquality)))))));
        var support = All("S", subsets, Call("DependsOn", Call("Phi", s), s));
        var neutral = All("S", subsets, Imp(Not(Call("IsClique", F.Id("G"), s)),
            All("x", xspace, Eqn(Phi(s, x), D(1)))));
        var reconstruction = All("x", xspace, Eqn(Fun(x),
            Seq(new Formula.Subscript(Prod, Seq(s, Colon, Sp, subsets)), Phi(s, x))));
        var factors = Some("Phi", Arr(subsets, Arr(xspace, a)),
            And(support, And(neutral, reconstruction)));
        var statement = All("V", Call("Type", F.Id("u")),
            All("Omega", Arr(v, Call("Type", F.Id("v"))),
                All("A", Call("Type", F.Id("w")),
                    Seq(OpenBracket, Call("CommGroup", a), CloseBracket, Sp,
                        OpenBracket, Call("Fintype", v), CloseBracket, Comma, Sp,
                        All("G", Call("SimpleGraph", v),
                            All("f", Arr(xspace, a),
                                new Formula.Logic(P(rectangle), FormulaLogicOperator.Iff, P(factors))))))));
        return Seq(Operatorname, Grp(F.Id("universe")), Sp,
            F.Id("u"), Sp, F.Id("v"), Sp, F.Id("w"), Semi, Sp, statement);
    }
}
