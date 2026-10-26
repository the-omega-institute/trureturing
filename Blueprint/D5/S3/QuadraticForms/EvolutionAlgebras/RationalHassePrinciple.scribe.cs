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
        string text, DescribeRole role = DescribeRole.Definition, bool literature = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution")) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static DocumentBlock.Describe RefDesc(string name, string title, string text,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational evolution products, perfect weak component ideals, and tensor-compatible reconstruction of unrestricted algebra isomorphisms.",
        H("Rational evolution algebras, components, and scalar extension"), Blocks(
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
                    + "entry in each row. It covers the zero-dimensional case without an extra hypothesis. "
                    + "This monomiality is Theorem 4 of Kaygorodov, Martín González and Viruel, "
                    + "arXiv:2610.22248v1, credited there to Elduque–Labra. Apply that result to the "
                    + "target product nu with natural bases c and b.map f: multiplication preservation "
                    + "makes b.map f natural, and the permutation and nonzero scalars give the stated "
                    + "row formula up to inverse indexing.",
                DescribeRole.Theorem, literature: true),
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
                    + "local-to-global implication or settle Conjecture 7.", DescribeRole.Theorem),
            RefDesc("WeakComponent", "Weak support components",
                "For a product mu on a vector space V over any field K and a finite basis b, "
                    + "WeakComponent(mu,b) is the quotient of the basis indices by the equivalence "
                    + "relation generated by a(mu,b,i,j) being nonzero. Thus arrow orientation is "
                    + "forgotten when forming components. Isolated vertices remain components, "
                    + "and an empty basis gives an empty component type."),
            RefDesc("componentIndex", "The component of a basis vector",
                "componentIndex(mu,b,i) is the equivalence class of i in WeakComponent(mu,b). "
                    + "A nonzero square coefficient from i to j makes these two classes equal."),
            RefDesc("coordinateSpace", "Coordinate submodules of a partition",
                "Let b be a finite basis over any field K, pi any function from its indices to "
                    + "a type Q, and q an element of Q. coordinateSpace(b,pi,q) is the actual "
                    + "K-submodule of vectors whose coordinates outside the fibre pi(i)=q vanish. "
                    + "No nonemptiness or surjectivity of pi is required."),
            RefDesc("restrictedProduct", "Restriction to a left ideal",
                "For a K-bilinear multiplication mu and an actual submodule S, suppose mu(x,y) "
                    + "belongs to S for every x in S and y in V. restrictedProduct(mu,S) is the "
                    + "bilinear multiplication on the subtype S whose underlying value at x,y is "
                    + "mu(x,y). The closure proof supplies the subtype membership, and imposes no "
                    + "associativity or unit law."),
            RefDesc("componentSpace", "The actual component submodule",
                "componentSpace(mu,b,q) is coordinateSpace(b,componentIndex(mu,b),q), an actual "
                    + "submodule of the original carrier V. The component ideal theorem identifies "
                    + "it with the span of the basis vectors whose indices belong to q."),
            RefDesc("componentProduct", "Multiplication on a component ideal",
                "For any field K and a natural finite basis b of mu, componentProduct(mu,b,q) "
                    + "restricts the original multiplication to componentSpace(mu,b,q). Its value "
                    + "at two component vectors is their product in the ambient algebra, with the "
                    + "proved component membership. Naturality suffices for closure; perfection "
                    + "is a separate premise of the component perfection theorem."),
            RefDesc("component_ideals_perfect", "Perfect mutually orthogonal component ideals",
                "Let K be any field, b a basis indexed by Fin(n), and mu a bilinear product. "
                    + "Assume Natural(mu,b) and Perfect(mu). For every weak component q, its actual "
                    + "submodule is precisely the span of the b(i) with componentIndex(i)=q. "
                    + "For x in that submodule and arbitrary y in V, both mu(x,y) and mu(y,x) "
                    + "belong to it. Its restricted product is perfect. Products between vectors "
                    + "in any two distinct component submodules vanish. The proof projects onto "
                    + "one coordinate fibre. Support stability makes the projection multiplicative, "
                    + "and its surjectivity transports the full pair-product span onto the component "
                    + "pair-product span. Empty dimensions and disconnected support are included.",
                DescribeRole.Theorem),
            RefDesc("isomorphic_of_component_matching", "Reconstruction from matched component ideals",
                "For any field K, take two bilinear products mu and nu on arbitrary carriers, "
                    + "with natural bases b and c indexed independently by Fin(n) and Fin(m). "
                    + "Suppose e is any bijection between their weak component types and each "
                    + "component q of mu has an unrestricted multiplicative K-linear equivalence "
                    + "to component e(q) of nu. Then mu and nu are isomorphic by an unrestricted "
                    + "multiplicative K-linear equivalence. No perfection assumption is needed in "
                    + "this direction. Coordinate projection identifies each whole space with the "
                    + "product of its component submodules; summation is the inverse. The given "
                    + "component maps and e then assemble the whole equivalence. The construction "
                    + "allows empty families, arbitrary component permutations, and repeated "
                    + "isomorphic components without choosing a canonical ordering.", DescribeRole.Theorem),
            RefDesc("isomorphism_matches_components", "Every isomorphism matches the actual component ideals",
                "Over any field K, let b,c be natural bases of mu,nu with independent finite sizes, "
                    + "and assume Perfect(nu). For every given K-linear equivalence f preserving "
                    + "multiplication on all vectors, there is a bijection E of weak components "
                    + "such that the image of componentSpace(mu,b,q) under f is exactly "
                    + "componentSpace(nu,c,E(q)). Restricting that same f gives an unrestricted "
                    + "isomorphism of the component products. Source perfection is unnecessary. "
                    + "Monomiality is derived from target perfection. Its coefficient equations "
                    + "show that the basis-index bijection preserves and reflects every nonzero "
                    + "square coefficient, because all scaling factors are units. It therefore "
                    + "induces E on weak components, and the basis-span images give the equality "
                    + "of actual submodules. No basis-preserving or graph-preserving premise is added.",
                DescribeRole.Theorem),
            RefDesc("baseChangedComponentProduct", "Component multiplication inside the tensor extension",
                "For fields K,F with a K-algebra structure on F, take mu with a natural finite "
                    + "basis b. Extend mu using LinearMap.BilinMap.baseChange on F tensor_K V "
                    + "and use the actual basis b.baseChange(F). For a weak component of this "
                    + "extended product, baseChangedComponentProduct is its restricted component "
                    + "multiplication on the actual component submodule. Naturality after "
                    + "extension follows from the pure-tensor multiplication law."),
            RefDesc("scalar_extension_component_reconstruction", "Tensor-compatible component reconstruction",
                "Let F be any field equipped with an algebra structure over the rationals. "
                    + "Let A,B be rational evolution algebras with rational natural bases b,c of "
                    + "independent finite sizes, and assume both rational products are perfect. "
                    + "There are bijections EA,EB from their rational weak components to the "
                    + "components of the actual tensor-extended products. These bijections send "
                    + "the rational component of each basis index to the extended component of "
                    + "that same index. For each rational component, its submodule base change "
                    + "is exactly the corresponding component submodule in the extended carrier. "
                    + "The tensor extension of its rational restricted multiplication is isomorphic "
                    + "to the restricted multiplication there by an unrestricted F-linear "
                    + "multiplicative equivalence. Every such extended component is perfect. "
                    + "Moreover, IsomorphicOver(F,A,B) holds exactly when there is a bijection e "
                    + "between the rational component types and unrestricted component "
                    + "isomorphisms from the component EA(q) of the first extended product to "
                    + "the component EB(e(q)) of the second, for every q. "
                    + "The actual square coefficients are the algebraMap images of the rational "
                    + "coefficients; injectivity preserves their zero pattern. The tensor inclusion "
                    + "of each component is injective by flatness over a field and has the required "
                    + "component image. Its multiplication law follows first on pure tensors and "
                    + "then by bilinearity. In the forward direction, the scalar coefficient "
                    + "comparison constructs a monomial linear equivalence and its component "
                    + "matching. The reverse direction uses whole-product reconstruction. "
                    + "The theorem includes zero dimension, disconnected support, arbitrary "
                    + "permutations, and repeated components. It proves no arithmetic descent "
                    + "from all completions and does not settle Conjecture 7.", DescribeRole.Theorem))));
}
