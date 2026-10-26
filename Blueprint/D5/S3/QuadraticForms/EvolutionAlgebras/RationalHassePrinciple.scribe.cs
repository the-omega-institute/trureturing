using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class RationalHassePrincipleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Some(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Negate(Formula a) => Seq(Neg, Sp, Open, a, Close);
    private static Formula Instance(Formula t, Formula body) =>
        Seq(OpenBracket, t, CloseBracket, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula K => V("K");
    private static Formula X => V("V");
    private static Formula Y => V("W");
    private static Formula Mu => V("mu");
    private static Formula Nu => V("nu");
    private static Formula N => V("n");
    private static Formula Nat => Call("NaturalNumbers");
    private static Formula Fin => Call("Fin", N);
    private static Formula Rat => Call("Rational");
    private static Formula Bundle => Call("RationalEvolutionAlgebra");
    private static Formula Apply(Formula p, Formula x, Formula y) => Call("Apply", p, x, y);
    private static Formula Prod(Formula k, Formula x) => Call("Product", k, x);
    private static Formula Basis(Formula x) => Call("Basis", Fin, K, x);
    private static Formula FieldContext(Formula body) =>
        All("K", V("Type"), Instance(Call("Field", K), body));
    private static Formula SpaceContext(string name, Formula body) =>
        All(name, V("Type"), Instance(Call("AddCommGroup", V(name)),
            Instance(Call("Module", K, V(name)), body)));
    private static Formula OneSpace(Formula body) => FieldContext(SpaceContext("V", body));
    private static Formula TwoSpaces(Formula body) =>
        FieldContext(SpaceContext("V", SpaceContext("W", body)));
    private static Formula ProductMap(Formula x) => Call("LinearMap", K, x,
        Call("LinearMap", K, x, x));
    private static Formula Preserves => All("x", X, All("y", X,
        Eq(Call("f", Apply(Mu, V("x"), V("y"))),
            Apply(Nu, Call("f", V("x")), Call("f", V("y"))))));
    private static Formula IsomorphismDefinition =>
        Some("f", Call("LinearEquiv", K, X, Y), Preserves);
    private static Formula MonomialConclusion => Some("sigma", Call("Perm", Fin),
        Some("t", Arrow(Fin, K), And(All("i", Fin, Ne(Call("t", V("i")), D(0))),
            All("i", Fin, All("j", Fin, Eq(
                Call("Coordinate", V("c"), Call("f", Call("b", V("j"))), V("i")),
                Call("IfThenElse", Eq(Call("sigma", V("i")), V("j")),
                    Call("t", V("i")), D(0))))))));
    private static Formula MonomialStatement => TwoSpaces(All("n", Nat,
        All("mu", Prod(K, X), All("nu", Prod(K, Y),
            All("b", Basis(X), All("c", Basis(Y),
                Imp(Call("Natural", Mu, V("b")), Imp(Call("Natural", Nu, V("c")),
                    Imp(Call("Perfect", Nu), All("f", Call("LinearEquiv", K, X, Y),
                        Imp(Preserves, MonomialConclusion)))))))))));
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula FinM => Call("Fin", V("m"));
    private static Formula IndexedBasis(Formula size, Formula scalarField, Formula carrier) =>
        Call("Basis", size, scalarField, carrier);
    private static Formula Coefficient(Formula product, Formula basis, Formula i, Formula j) =>
        Call("structureCoefficient", product, basis, i, j);
    private static Formula ComparisonConclusion(Formula scalarField, Formula source, Formula target,
        Formula sourceBasis, Formula targetBasis, bool scalarExtension)
    {
        var i = V("i"); var j = V("j");
        var ai = Coefficient(source, sourceBasis, i, j);
        var bi = Coefficient(target, targetBasis, Call("e", i), Call("e", j));
        if (scalarExtension)
        {
            ai = Call("algebraMap", Rat, scalarField, ai);
            bi = Call("algebraMap", Rat, scalarField, bi);
        }
        var di = Call("Value", Call("d", i));
        var dj = Call("Value", Call("d", j));
        return Some("e", Call("Equiv", Fin, FinM),
            Some("d", Arrow(Fin, Call("Units", scalarField)),
                All("i", Fin, All("j", Fin,
                    Eq(Mul(ai, dj), Mul(Mul(di, di), bi))))));
    }
    private static Formula ComparisonStatement => TwoSpaces(All("n", Nat, All("m", Nat,
        All("mu", Prod(K, X), All("nu", Prod(K, Y),
            All("b", IndexedBasis(Fin, K, X), All("c", IndexedBasis(FinM, K, Y),
                Imp(Call("Natural", Mu, V("b")), Imp(Call("Natural", Nu, V("c")),
                    Imp(Call("Perfect", Nu), Iff(Call("Isomorphic", Mu, Nu),
                        ComparisonConclusion(K, Mu, Nu, V("b"), V("c"), false))))))))))));
    private static Formula ScalarComparisonStatement
    {
        get
        {
            var scalarField = V("F");
            var source = Call("multiplication", V("A"));
            var target = Call("multiplication", V("B"));
            var body = Imp(Call("Natural", source, V("b")),
                Imp(Call("Natural", target, V("c")), Imp(Call("Perfect", target),
                    Iff(Call("IsomorphicOver", scalarField, V("A"), V("B")),
                        ComparisonConclusion(scalarField, source, target, V("b"), V("c"), true)))));
            body = All("b", IndexedBasis(Fin, Rat, Call("Carrier", V("A"))),
                All("c", IndexedBasis(FinM, Rat, Call("Carrier", V("B"))), body));
            body = All("A", Bundle, All("B", Bundle, All("n", Nat, All("m", Nat, body))));
            return All("F", V("Type"), Instance(Call("Field", scalarField),
                Instance(Call("Algebra", Rat, scalarField), body)));
        }
    }
    private static Formula ClaimFormula => Some("A", Bundle, Some("B", Bundle,
        And(Call("Perfect", Call("multiplication", V("A"))),
            And(Call("Perfect", Call("multiplication", V("B"))),
                And(Call("IsomorphicOver", Call("Real"), V("A"), V("B")),
                    And(All("p", Nat, Imp(Call("Prime", V("p")),
                        Call("IsomorphicOver", Call("Padic", V("p")), V("A"), V("B")))),
                        Negate(Call("Isomorphic", Call("multiplication", V("A")),
                            Call("multiplication", V("B"))))))))));
    private static DocumentBlock.Describe Desc(string name, string title, Formula formula,
        string text, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational evolution products, actual tensor scalar extension, and two-way monomial coefficient comparisons for full algebra isomorphisms.",
        H("Rational evolution algebras and scalar extension"), Blocks(
            Paragraph(Text("Multiplication is bilinear and may be nonassociative and nonunital. "
                + "A natural basis is defined over the stated ground field. All finite dimensions, "
                + "including zero, and disconnected support graphs are allowed. "
                + "The Hasse existence proposition below is Conjecture 7 of Kaygorodov, Martin Gonzalez "
                + "and Viruel, arXiv:2610.22248v1, https://arxiv.org/html/2610.22248v1#Thmconjecture7. "
                + "Monomiality is an algebraic reduction; it does not supply the local-to-global implication.")),
            Desc("Product", "Bilinear multiplication", OneSpace(
                Eq(Prod(K, X), ProductMap(X))),
                "Product(K,V) is the type of K-bilinear maps from V times V to V. "
                    + "It imposes neither associativity nor a unit."),
            Desc("Perfect", "Perfection", OneSpace(All("mu", Prod(K, X),
                Iff(Call("Perfect", Mu), Eq(Call("SpanOfAllPairProducts", K, Mu), V("Top"))))),
                "Perfect(mu) means span_K {mu(x,y) : x,y in V}=V. The span contains all pair products."),
            Desc("Natural", "A natural basis", OneSpace(All("n", Nat,
                All("mu", Prod(K, X), All("b", Basis(X), Iff(Call("Natural", Mu, V("b")),
                    All("i", Fin, All("j", Fin, Imp(Ne(V("i"), V("j")),
                        Eq(Apply(Mu, Call("b", V("i")), Call("b", V("j"))), D(0)))))))))),
                "Natural(mu,b) requires mu(b(i),b(j))=0 for every unequal pair of indices. "
                    + "The supplied b is already an ordinary basis."),
            Desc("Isomorphic", "The full algebra isomorphism relation", TwoSpaces(
                All("mu", Prod(K, X), All("nu", Prod(K, Y),
                    Iff(Call("Isomorphic", Mu, Nu), IsomorphismDefinition)))),
                "An isomorphism is any K-linear equivalence f satisfying f(mu(x,y))=nu(f(x),f(y)) "
                    + "for every x,y. No prescribed permutation, graph, or basis preservation is required."),
            Desc("RationalEvolutionAlgebra", "Finite rational evolution algebras",
                Eq(Bundle, Call("FiniteDimensionalRationalVectorSpacesWithBilinearProductAndNaturalBasis")),
                "The carrier is an arbitrary type with an additive commutative group and rational "
                    + "module structure, together with finite dimensionality, a bilinear multiplication, "
                    + "and existence of n and a natural rational basis indexed by Fin(n). "
                    + "Perfection is a separate predicate, not part of this bundle."),
            Desc("IsomorphicOver", "Actual scalar extension", All("F", V("Type"),
                Instance(Call("Field", V("F")), Instance(Call("Algebra", Rat, V("F")),
                    All("A", Bundle, All("B", Bundle,
                        Iff(Call("IsomorphicOver", V("F"), V("A"), V("B")),
                            Call("Isomorphic", Call("BilinearBaseChange", V("F"),
                                Call("multiplication", V("A"))), Call("BilinearBaseChange", V("F"),
                                Call("multiplication", V("B")))))))))),
                "The two carriers are F tensor_Q A and F tensor_Q B. Their multiplications are "
                    + "Mathlib LinearMap.BilinMap.baseChange: (a tensor x)(b tensor y)="
                    + "ab tensor mu(x,y), extended bilinearly to every tensor. "
                    + "IsomorphicOver uses arbitrary F-linear multiplication-preserving equivalences."),
            Desc("claim", "The full Hasse failure existence proposition", ClaimFormula,
                "There exist finite-dimensional perfect rational evolution algebras A and B "
                    + "isomorphic after extension to the real numbers and to Q_p for every rational "
                    + "prime p, yet not rationally isomorphic. The quantifier ranges over every prime; "
                    + "no finite list or dimension bound is substituted. This node states the conjecture "
                    + "and asserts no proof or refutation."),
            Desc("isomorphism_monomial", "Isomorphisms are forced to be monomial", MonomialStatement,
                "For any field K and two natural bases of equal finite size, perfection of the target "
                    + "forces the matrix of a multiplication isomorphism to have at most one "
                    + "nonzero entry in each row. Surjectivity makes every row nonzero; "
                    + "injectivity makes every column nonzero. A finite permutation and nonzero row "
                    + "scalars result. Source perfection is unnecessary. The two products and bases "
                    + "may be different. The proof uses all pair products to show injectivity of the "
                    + "target structure map, then constructs the permutation from the unique nonzero "
                    + "entry in each row. It covers the zero-dimensional case without an extra hypothesis.",
                DescribeRole.Theorem),
            Desc("structureCoefficient", "Square structure coefficients", OneSpace(All("n", Nat,
                All("mu", Prod(K, X), All("b", Basis(X), All("i", Fin, All("j", Fin,
                    Eq(Coefficient(Mu, V("b"), V("i"), V("j")),
                        Call("Coordinate", V("b"), Apply(Mu, Call("b", V("i")),
                            Call("b", V("i"))), V("j"))))))))),
                "The coefficient a(mu,b,i,j) is the j-th coordinate of mu(b(i),b(i)) in b. "
                    + "The first index selects the squared basis vector and the second its output coordinate."),
            Desc("isomorphic_iff_monomial_equations", "Full isomorphisms and monomial equations",
                ComparisonStatement,
                "Let b and c be natural bases indexed independently by Fin(n) and Fin(m) over any field K, "
                    + "with perfect target multiplication nu. An arbitrary multiplicative linear equivalence "
                    + "exists exactly when there are a bijection e:Fin(n) to Fin(m) and units d(i) such that "
                    + "a(mu,b,i,j)d(j)=d(i)^2 a(nu,c,e(i),e(j)) for every i,j. The corresponding map sends "
                    + "b(i) to d(i)c(e(i)). A given linear equivalence forces n=m by preservation of finrank; "
                    + "monomiality then gives e as the inverse of its target-row permutation. Comparing "
                    + "the image of each square in coordinate e(j) gives the displayed orientation. Conversely, "
                    + "reindexing and scaling c by units constructs a linear bijection. The equations prove "
                    + "square preservation, and naturality proves preservation of every mixed basis product. "
                    + "Bilinear extensionality extends this to all vectors. No source perfection, positive "
                    + "dimension, connected support, or prescribed permutation is required.", DescribeRole.Theorem),
            Desc("isomorphic_over_iff_monomial_equations", "The comparison on tensor scalar extensions",
                ScalarComparisonStatement,
                "For any field F with a rational algebra structure, take rational natural bases b,c of A,B "
                    + "with independent finite sizes and perfect rational target B. The actual relation "
                    + "IsomorphicOver(F,A,B) is equivalent to the same monomial equations with every rational "
                    + "structure coefficient mapped to F. The bases are b.baseChange(F), c.baseChange(F), "
                    + "whose vectors are 1 tensor b(i) and 1 tensor c(j). Their products use precisely "
                    + "LinearMap.BilinMap.baseChange, so their square coefficients are the scalar images "
                    + "of the rational coefficients. Perfection ascends because tensors of rational pair "
                    + "products are pair products after extension and their F-span is the whole tensor space. "
                    + "Local perfection is therefore a consequence, rather than an additional assumption. "
                    + "This applies to the real field and to Q_p for every prime, including zero-dimensional "
                    + "algebras and disconnected supports. These equivalences do not establish the arithmetic "
                    + "local-to-global implication or settle Conjecture 7.", DescribeRole.Theorem))));
}
