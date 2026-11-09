using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class DirectSumHeredityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary evolution algebras need not have a hereditary direct sum.",
        H("Direct sums and intrinsic evolution subalgebras"),
        Blocks(
            Node("inheritedProduct", InheritedFormula(),
                "A multiplication-closed linear subspace has the restricted bilinear multiplication. The displayed subtype value includes the closure proof; no unit, associativity or extension of a basis is required.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("Hereditary", HereditaryFormula(),
                "Question 12 (Hereditary evolution algebras), §2.2.2, p. 22: “Characterise the evolution algebras all of whose subalgebras are evolution algebras. Is this property detected by the graphs? Is it preserved by tensor products and direct sums? What about ideals?” A subalgebra is a linear subspace closed under multiplication. Every such subspace, including zero and the whole space, must admit its own natural basis; that basis need not extend to the ambient algebra.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("directSumProduct", DirectSumFormula(),
                "The finite direct sum has componentwise multiplication. The displayed pair is the full value of the bilinear map at two vectors.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", Eqn(Name("claim"), ClaimBody()),
                "Question 12 (Hereditary evolution algebras), §2.2.2, p. 22: “Characterise the evolution algebras all of whose subalgebras are evolution algebras. Is this property detected by the graphs? Is it preserved by tensor products and direct sums? What about ideals?” The formula selects the affirmative direct-sum assertion. The field K is arbitrary, and m and n range over all finite dimensions, including zero. The coordinate spaces are Fin m → K and Fin n → K. IsEvolutionAlgebra is the intrinsic predicate from DerivationAnnihilatorObstruction: a commutative bilinear multiplication with an actual Module.Basis of pairwise zero mixed products.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                "Over ℚ take dimensions four and three, with symmetric forms diag(1,−1,1,−1) and diag(1,−1,1). Multiply each scalar output by (1,1,0,0) and (1,1,0), respectively. The orthogonal-basis theorem applied on every closed subspace makes both factors hereditary. In their direct sum impose a₀ = a₁, b₀ = b₁ and b₂ = a₂ + a₃. Zero mixed products in a natural basis would force the sum and difference coordinate functionals to be proportional. The vectors ((0,0,1,0),(0,0,1)) and ((0,0,0,1),(0,0,1)) contradict that proportionality. Thus direct-sum preservation fails. Graph detection, tensor products, ideals, characteristic two, minimal dimensions and the full characterization remain separate questions.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kmvq12"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Name(name), args);
    private static Formula Qualified(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula SubtypeValue(Formula a, Formula proof) => Seq(Langle, a, Comma, Sp, proof, Rangle);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula At(Formula a, byte coordinate) => Seq(a, Dot, D(coordinate));
    private static Formula Mem(Formula a, Formula set) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, set);
    private static Formula Type => Name("Type");
    private static Formula K => X("K");
    private static Formula V => X("V");
    private static Formula W => X("W");
    private static Formula S => X("S");
    private static Formula LMap(Formula a, Formula b) => Call("LinearMap", K, a, b);
    private static Formula Product(Formula carrier) => LMap(carrier, LMap(carrier, carrier));
    private static Formula Space(Formula n) => Arrow(Call("Fin", n), K);
    private static Formula Closed() => All(X("x"), V, All(X("y"), V,
        Imp(Mem(X("x"), S), Imp(Mem(X("y"), S), Mem(Apply(Mu, X("x"), X("y")), S)))));
    private static Formula AlgebraContext(Formula body) => All(K, Type, Instance(Call("Field", K),
        All(V, Type, Instance(Call("AddCommGroup", V), Instance(Call("Module", K, V), body)))));
    private static Formula Evolution(Formula product) => Apply(
        Qualified("DerivationAnnihilatorObstruction", "IsEvolutionAlgebra"), product);
    private static Formula InheritedFormula() => AlgebraContext(All(Mu, Product(V),
        All(S, Call("Submodule", K, V), All(X("closed"), Closed(),
        All(X("x"), S, All(X("y"), S,
        Eqn(Call("inheritedProduct", Mu, S, X("closed"), X("x"), X("y")),
            SubtypeValue(Apply(Mu, Val(X("x")), Val(X("y"))),
                Apply(X("closed"), Val(X("x")), Val(X("y")),
                    Apply(Qualified("Subtype", "property"), X("x")),
                    Apply(Qualified("Subtype", "property"), X("y")))))))))));
    private static Formula HereditaryFormula() => AlgebraContext(All(Mu, Product(V),
        Eqn(Call("Hereditary", Mu), All(S, Call("Submodule", K, V),
            All(X("closed"), Closed(), Evolution(Call("inheritedProduct", Mu, S, X("closed"))))))));
    private static Formula DirectSumFormula() => AlgebraContext(All(W, Type,
        Instance(Call("AddCommGroup", W), Instance(Call("Module", K, W),
        All(Mu, Product(V), All(Nu, Product(W),
        All(X("x"), Seq(V, Sp, Times, Sp, W), All(X("y"), Seq(V, Sp, Times, Sp, W),
            Eqn(Call("directSumProduct", Mu, Nu, X("x"), X("y")),
                Pair(Apply(Mu, At(X("x"), 1), At(X("y"), 1)),
                    Apply(Nu, At(X("x"), 2), At(X("y"), 2))))))))))));
    private static Formula ClaimBody() => All(K, Type, Instance(Call("Field", K),
        All(X("m"), Seq(Mathbb, Grp(X("N"))), All(X("n"), Seq(Mathbb, Grp(X("N"))),
        All(Mu, Product(Space(X("m"))), All(Nu, Product(Space(X("n"))),
        Imp(Evolution(Mu), Imp(Evolution(Nu),
        Imp(Call("Hereditary", Mu), Imp(Call("Hereditary", Nu),
            Call("Hereditary", Call("directSumProduct", Mu, Nu))))))))))));
}
