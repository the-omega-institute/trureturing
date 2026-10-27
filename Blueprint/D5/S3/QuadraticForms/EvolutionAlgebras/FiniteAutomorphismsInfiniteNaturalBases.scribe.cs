using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class FiniteAutomorphismsInfiniteNaturalBasesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.";
    private static readonly LibraryNoteRef Survey = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static readonly LibraryNoteRef Classification = LibraryNoteRef.Create("D5/L/QuadraticForms/goncalves2018twodimensional");
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [..args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula C => X("Complex");
    private static Formula A => Call("Prod", C, C);
    private static Formula Index => Call("Fin", D(2));
    private static Formula Product(Formula a) => Call("LinearMap", C, a, Call("LinearMap", C, a, a));
    private static Formula Basis(Formula a) => Call("Basis", Index, C, a);
    private static Formula Natural(Formula m, Formula b) => All("i", Index, All("j", Index,
        Imp(Rel(X("i"), FormulaRelationOperator.NotEqual, X("j")),
            Equal(App(m, App(b, X("i")), App(b, X("j"))), D(0)))));
    private static Formula Nondegenerate(Formula m) => All("x", A,
        Imp(All("y", A, Equal(App(m, X("x"), X("y")), D(0))), Equal(X("x"), D(0))));
    private static Formula Full
    {
        get
        {
            var m = X("m");
            var body = And(Call("Finite", App(Seq(Name("EvolutionAutomorphismControl"), Dot, Name("Aut")), m)),
                Call("Infinite", Call("Quotient", Call("basisSetoid", m))));
            body = And(Call("Nonempty", Call("NaturalBasis", m)), body);
            body = And(Nondegenerate(m), body);
            body = And(All("x", A, All("y", A,
                Equal(App(m, X("x"), X("y")), App(m, X("y"), X("x"))))), body);
            body = And(Equal(Call("finrank", C, A), D(2)), body);
            return Some("m", Product(A), body);
        }
    }
    private static Formula WithCarrier(Formula body) => All("V", X("Type"), Seq(
        OpenBracket, Call("AddCommGroup", X("V")), CloseBracket, Sp,
        OpenBracket, Call("Module", C, X("V")), CloseBracket, Comma, Sp,
        All("m", Product(X("V")), body)));
    private static DocumentBlock.Describe Desc(string name, string title, Formula formula, string text,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role,
            openProblemResolutionClaim: resolution);

    public DocumentDefinition Create()
    {
        var m = X("m");
        var v = X("V");
        var b = X("b");
        var c = X("c");
        var relation = Some("sigma", Call("Perm", Index),
            Some("u", Seq(Index, Sp, To, Sp, Call("Units", C)),
                All("i", Index, Equal(App(b, X("i")),
                    Seq(App(X("u"), X("i")), Sp, Cdot, Sp, App(c, App(X("sigma"), X("i"))))))));
        var naturalType = Call("NaturalBasis", m);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite full automorphisms coexist with infinitely many natural bases modulo arbitrary permutation and independent nonzero scaling.",
            H("A positive answer to Question 14's final interrogative"), Blocks(
                Paragraph(Text("Question 14 in section 2.2.2 of arXiv:2610.22248v1 asks: Describe the set of natural bases (up to permutation and scaling) of a non-degenerate evolution algebra. When is it finite? Can it be infinite for an algebra whose automorphism group is finite? "
                    + "The result answers the complete final sentence only. The survey works over a field and assumes finite dimension unless stated otherwise. Complex scalars are permitted; no assertion for every field is needed. Non-degenerate means the annihilator is zero. Aut means all invertible linear maps preserving multiplication, or the field-valued points of the automorphism group scheme, rather than a chosen monomial subgroup.")),
                Desc("NaturalBasis", "All actual natural bases in the canonical two-element presentation",
                    WithCarrier(Equal(naturalType, Seq(OpenBrace, b, Colon, Basis(v), Sp, Mid, Sp, Natural(m, b), CloseBrace))),
                    "An element contains a Module.Basis, including linear independence and spanning, and the zero mixed-product proof. It is not merely an ordered pair of vectors. For the witness the dimension is two. Every vector-space basis is finite by Module.Finite.finite_basis and has exactly two elements by Module.finrank_eq_card_basis. It can be reindexed by Fin 2 using Basis.reindex. Any two such choices differ by a permutation of Fin 2. Thus after the permutation quotient this canonical indexing represents the source domain of actual bases; it adds no identification and omits no basis. The theorem uses this presentation, without claiming a separately compiled equivalence across all possible index types.",
                    AssessedProvenance.FromRepo(Survey, Classification)),
                Desc("basisSetoid", "Exactly permutation and independent nonzero rescaling",
                    WithCarrier(All("b", naturalType, All("c", naturalType,
                        Iff(Call("Rel", Call("basisSetoid", m), b, c), relation)))),
                    "Every permutation is allowed, and each vector has its own arbitrary complex unit. Over a field each nonzero scalar yields Units.mk0 and every unit has nonzero value, so these are exactly the independent nonzero scalars in the source. Identity, inverse permutation with inverse units, and composition with product units prove reflexivity, symmetry and transitivity. Quotient identifies precisely this relation. There is no quotient by algebra automorphisms, no restriction to real rescalings, and no normalization of a basis before taking the quotient.",
                    AssessedProvenance.FromRepo(Survey, Classification)),
                Desc("mu", "The older algebra with one-dimensional square",
                    All("x", A, All("y", A, Equal(App(X("mu"), X("x"), X("y")),
                        Call("pair", Add(Mul(Call("fst", X("x")), Call("fst", X("y"))),
                            Mul(Call("snd", X("x")), Call("snd", X("y")))), D(0))))),
                    "The carrier is Complex times Complex and mu is complex linear in each argument; neither coefficient is conjugated. Its standard coordinate basis has e(0)^2=e(0), e(1)^2=e(0), and zero mixed products. The coordinate e(0) is u and e(1) is v in the 2018 algebra A_(8,1); the survey's Proposition 14 at n=1 uses the order (e(1),u). The square lies in the first coordinate line and contains e(0), so the algebra is non-perfect. Testing a vector against e(0) and e(1) proves that its annihilator is zero. Isotropic square-zero vectors are not confused with annihilator elements. This is a bilinear, possibly nonassociative algebra, and no associative AlgEquiv is used.",
                    AssessedProvenance.FromLiterature(Classification)),
                Paragraph(Text("The full-group proof starts with an arbitrary member of EvolutionAutomorphismControl.Aut mu, whose defining subgroup contains every invertible complex-linear multiplication-preserving map. The image of e(0) is a nonzero idempotent and must equal e(0). Its mixed product with the image of e(1) forces that image's first coordinate to vanish. Preservation of e(1)^2=e(0) forces its second coordinate d to satisfy d*d=1. Hence d is either 1 or -1, and linearity determines the map everywhere. Its value of d gives an injection into Bool, proving finiteness. This full-group classification is a published ingredient.")),
                Paragraph(Text("For every natural number n, let t=n+1 and take u(n)=(1,t), v(n)=(-t,1). Their mixed product is zero. The matrix with these columns has determinant 1+t*t, a positive natural integer embedded in Complex, hence nonzero. The explicit inverse sends (x,y) to ((x+t*y)/(1+t*t),(-t*x+y)/(1+t*t)); both inverse laws are proved. Mapping the standard basis along this linear equivalence therefore constructs an actual natural basis for every n.")),
                Paragraph(Text("Suppose the classes for n and m coincide, and put s=m+1. The exact quotient relation sends u(n) to an arbitrary complex scalar multiple of either u(m) or v(m). In the first case the first coordinates force the scalar to be one, then t=s and n=m. In the swapped case the second coordinates force the scalar to be t, and the first coordinates give t*s=-1. This contradicts the nonzero positive natural integer t*s+1 embedded in Complex. Thus n maps injectively into the quotient of all natural bases. Infinite.of_injective gives the required infinite quotient, rather than just infinitely many ordered or rescaled representatives.")),
                Desc("result", "The full source-faithful existence conjunction", Full,
                    "The witness is the published mu on the two-dimensional complex space. The six conjuncts state dimension two, commutativity, zero annihilator, existence of an actual natural basis, finiteness of the full linear multiplication-automorphism group, and infinitude of the exact natural-basis quotient. Complex is a permitted field; the LinearMap types supply bilinearity.",
                    AssessedProvenance.FromRepo(Survey, Classification), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("kaygorodov-martin-gonzalez-viruel-2026-finite-aut-infinite-natural-bases"),
                        ResolutionKind.Proved)),
                Paragraph(Text("The 2018 classification, Lemma 3.15 and section 5.1, already provides this algebra, the arbitrary-natural-basis determinant and orthogonality equations, and its finite full automorphism group. Non-degenerate evolution algebras, arXiv:2303.00862v1, Theorem 26 and Remark 29, gives the same finite-group ingredient. Natural families in evolution algebras, arXiv:2006.14460v1, Corollary 2.13 and Proposition 2.16, supplies structural basis results. Solenoids in automorphism groups of evolution algebras, arXiv:2505.14584v1, Example 6.3, gives an older infinite quotient example with nonzero annihilator and infinite full group. These ingredients receive prior credit. No prior published whole answer was found in the bounded search; worldwide absence and priority remain unverified. Authenticated code search was unavailable, so no search-complete claim is made. The general description and finiteness criterion asked in Q14's first two sentences remain outside this result."))), []));
    }
}
