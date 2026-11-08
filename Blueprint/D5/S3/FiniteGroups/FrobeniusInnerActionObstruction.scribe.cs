using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrobeniusInnerActionObstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026finitecharacters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over any field, a fixed-point-free automorphism can act internally on a finite-dimensional simple group-algebra quotient only through augmentation.",
        H("Inner actions and the augmentation obstruction"),
        Blocks(
            Node("trivial_of_inner_image", "Rigidity inside the representation image", ImageStatement(),
                "Let k be any field, N a finite group and V a finite-dimensional k-representation whose k[N]-module is simple. Let phi be an automorphism with phi(n) = n only for n = 1. Suppose r and s in k[N] act as mutually inverse endomorphisms of V and rho(r) rho(n) = rho(phi(n)) rho(r) for every n. Then every rho(n) is the identity. The inverse identities are required only in the representation image; r and s need not be units of k[N].",
                "Choose E as an algebraic closure of a universe lift of k and extend V to X = E tensor_k V. Write R = k[N], B = E[N], and psi : R -> B for coefficient extension. The existing ext_isotypic theorem supplies semisimple, V-isotypic support for X as an R-module: pure tensors generate images of R-linear maps V -> X. This is original k[N]-support. It asserts no E[N]-semisimplicity, and the proof never assumes X is a semisimple B-module.",
                "The nonzero finite-dimensional B-module X contains a nonzero simple B-submodule Y. Its R-support is inherited through supported_submodule. Hence Y contains a simple R-submodule S isomorphic to V, giving an injective R-linear map j : V -> S -> Y. Both psi(r) and psi(s) preserve this same Y because Y is a B-submodule. Their restricted E-linear operators T and Tinv are mutually inverse: coefficient extension transports both image inverse identities. Thus the implementer cannot merely permute the simple constituents under consideration.",
                "The compatibility of coefficient extension with the representation algebra homomorphism transports the intertwining equation to Y. The consumed private ofModule'_action helper identifies its B-module action with the algebra action of its associated representation. Apply trivial_of_equiv_fixedPointFree_of_isAlgClosed to this simple finite-dimensional E-representation and T. It makes N act trivially on Y. R-linearity and injectivity of j then force N to act trivially on V."),
            Node("inner_action_obstruction", "A simple quotient admitting an inner action is the scalar field", QuotientStatement(),
                "Let k be any field, N a finite group, and A a unital simple k-algebra finite-dimensional over k. Let q : k[N] -> A be a surjective k-algebra homomorphism, phi a fixed-point-free automorphism of N, and u a unit of A satisfying q([phi(n)]) = u q([n]) u^(-1) for every n. Then all q([n]) equal one, q equals the composite k[N] --augmentation--> k --Algebra.ofId--> A, and there exists a k-algebra equivalence A -> k. Here [n] means MonoidAlgebra.of k N n. The augmentation is the existing public D5.S3.ArithUnits.MinacNguyenTanQuestion35.augmentation, sending each [n] to one.",
                "Finite-dimensionality makes A Artinian, so its nonzero regular module has a simple submodule U. Simplicity of the ring makes the unital action A -> End_k(U) faithful. Surjectivity of q makes the induced k[N]-module U simple and supplies preimages r, s of u, u^(-1). Their operators satisfy both inverse identities and the required intertwining equation. The image-rigidity theorem therefore makes N act trivially on U. Faithfulness detects q([n]) = 1 in A itself. The group-algebra universal property gives the exact augmentation factorization. Since q is surjective, the scalar map k -> A is surjective; it is also injective, yielding the displayed algebra equivalence.",
                "An external intertwiner V -> V twisted by phi need not belong to the image algebra. After scalar extension it need not preserve a chosen simple B-submodule. The internal implementer and its inverse do preserve that submodule, which is the extra structure used here. The result requires no splitting-field, perfectness, characteristic, coprimality, separability or Schur-index hypothesis; it also assumes no semisimplicity of E[N] or of the whole extended representation.",
                "For the arithmetic Frobenius direction, if a conjugation from an ambient group induces a fixed-point-free automorphism on N and is implemented by a unit in a simple quotient of k[N], that quotient must be augmentation. Applying this ingredient to representation images still requires proving that the implementer belongs to the relevant image algebra. The stronger normalized-degree statement remains open; this theorem does not prove its missing arithmetic or image-membership steps. The argument is a repository derivation using the existing fixed-point-free trace rigidity and original-module support. The cited Library note supplies the classical representation-theoretic background and provenance, not a claim that this exact synthesis is a new result in the literature."))));

    private static DocumentBlock Node(string name, string title, Formula statement, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("frobenius-inner-" + name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/FiniteGroups/FrobeniusInnerActionObstruction." + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);

    private static Formula ImageStatement()
    {
        Formula k = F.Id("k"), n = F.Id("N"), v = F.Id("V"), rho = F.Id("rho"), phi = F.Id("phi");
        Formula r = F.Id("r"), s = F.Id("s"), x = F.Id("n");
        Formula algebra = GroupAlgebra(k, n);
        Formula action = App(Q("Representation", "asAlgebraHom"), rho);
        Formula result = App(Q("Representation", "IsTrivial"), rho);
        result = All("hint", All("n", n,
            Eq(Mul(App(action, r), App(rho, x)), Mul(App(rho, App(phi, x)), App(action, r)))), result);
        result = All("hsr", Eq(Mul(App(action, s), App(action, r)), D(1)), result);
        result = All("hrs", Eq(Mul(App(action, r), App(action, s)), D(1)), result);
        result = All("s", algebra, result);
        result = All("r", algebra, result);
        result = All("hphi", FixedFree(n, phi), result);
        result = All("phi", App(F.Id("MulAut"), n), result);
        result = All("hrho", App(F.Id("IsSimpleModule"), algebra,
            App(Q("Representation", "asModule"), rho)), result);
        result = All("rho", App(F.Id("Representation"), k, n, v), result);
        result = Instance(App(Q("Module", "Finite"), k, v), result);
        result = Instance(App(F.Id("Module"), k, v), result);
        result = Instance(App(F.Id("AddCommGroup"), v), result);
        result = Instance(App(F.Id("Finite"), n), result);
        result = Instance(App(F.Id("Group"), n), result);
        result = Instance(App(F.Id("Field"), k), result);
        return All("k", TypeStar(), All("N", TypeStar(), All("V", TypeStar(), result)));
    }

    private static Formula QuotientStatement()
    {
        Formula k = F.Id("k"), n = F.Id("N"), a = F.Id("A"), q = F.Id("q"), phi = F.Id("phi");
        Formula x = F.Id("n"), u = F.Id("u");
        Formula basis = App(Q("MonoidAlgebra", "of"), k, n);
        Formula augmentation = App(Q("D5.S3.ArithUnits.MinacNguyenTanQuestion35", "augmentation"), k, n);
        Formula factor = App(Q("AlgHom", "comp"), App(Q("Algebra", "ofId"), k, a), augmentation);
        Formula equiv = App(F.Id("AlgEquiv"), k, a, k);
        Formula result = And(All("n", n, Eq(App(q, App(basis, x)), D(1))),
            And(Eq(q, factor), App(F.Id("Nonempty"), equiv)));
        result = All("hu", All("n", n, Eq(App(q, App(basis, App(phi, x))),
            Mul(Mul(App(Q("Units", "val"), u), App(q, App(basis, x))),
                App(Q("Units", "val"), App(Q("Inv", "inv"), u))))), result);
        result = All("u", App(F.Id("Units"), a), result);
        result = All("hphi", FixedFree(n, phi), result);
        result = All("phi", App(F.Id("MulAut"), n), result);
        result = All("hq", App(Q("Function", "Surjective"), q), result);
        result = All("q", App(F.Id("AlgHom"), k, GroupAlgebra(k, n), a), result);
        result = Instance(App(Q("Module", "Finite"), k, a), result);
        result = Instance(App(F.Id("IsSimpleRing"), a), result);
        result = Instance(App(F.Id("Algebra"), k, a), result);
        result = Instance(App(F.Id("Ring"), a), result);
        result = Instance(App(F.Id("Finite"), n), result);
        result = Instance(App(F.Id("Group"), n), result);
        result = Instance(App(F.Id("Field"), k), result);
        return All("k", TypeStar(), All("N", TypeStar(), All("A", TypeStar(), result)));
    }

    private static Formula FixedFree(Formula n, Formula phi) =>
        All("n", n, Imp(Eq(App(phi, F.Id("n")), F.Id("n")), Eq(F.Id("n"), D(1))));
    private static Formula TypeStar() => Seq(F.Id("Type"), Star);
    private static Formula GroupAlgebra(Formula k, Formula n) => App(F.Id("MonoidAlgebra"), k, n);
    private static Formula Q(string owner, string name)
    {
        string[] parts = owner.Split('.');
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (string part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return Seq(result, Dot, Operatorname, Grp(F.Id(name)));
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
