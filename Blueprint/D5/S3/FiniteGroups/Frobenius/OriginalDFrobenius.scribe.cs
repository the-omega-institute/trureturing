using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDFrobeniusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius divisibility and actual regular coordinates over the original Schur division ring.",
        H("The original division ring"),
        Blocks(
            Node("index_dvd_originalD_finrank", RankStatement(),
                "Let G be finite, N normal, and suppose that every conjugation by g outside N fixes only the identity in N. Let rho be a finite-dimensional irreducible representation over an arbitrary field k, whose restriction to N is nontrivial. Set W = rho.asModule and D = Module.End k[G] W, acting on the left by evaluation. Then N.index divides Module.finrank D W. The scalar, group and carrier universes are independent.",
                "Choose a simple restricted constituent and its actual isotypic component U. The original-D Clifford theorem gives dim_D W = [G:H] dim_D U for its actual inertia H. The Hall argument from Yawara Ishida's KernelComplement, revision ba8ec35982ceecbd31ca987cbe0cee30477f4883, derives an actual complement C from the fixed-point-free hypothesis; pinned Mathlib supplies Schur-Zassenhaus. Restrict C to J = C intersect H. Then N is contained in H, N and J complement each other in H, and |J| = [H:N].",
                "The actual image of k[N] on U is simple because U is semisimple and isotypic. Its center F is a field. Actual original-D endomorphisms commute with this image, so the center acts by D-linear operators. Actual J operators act covariantly on these center operators. The checked center-kernel theorem proves that J acts faithfully on F. Taking K = F^J, the fixed-field Galois instance and the actual equivalence J = Gal(F/K) are supplied by Mathlib. Descent and a normal basis give dim_D U = |J| dim_D S, with no K-to-D embedding or F/D scalar tower. Index multiplication yields the asserted divisibility.",
                "Normal-N invariants are a G-subrepresentation. Global irreducibility and nontrivial N action force them to be zero; consequently the nonzero actual component has nontrivial restricted action. No complement, faithfulness, semisimplicity, decomposition, normal basis, characteristic condition, splitting field, or commutativity of D is assumed."),
            Node("exists_complement_originalD_regular", RegularStatement(),
                "Under the same hypotheses there exist an actual complement C, a D-submodule S of W, and a D-linear equivalence E : W -> (C -> S) satisfying E(rho(c)v)(x) = E(v)(c^(-1)x). This is an equivalence for the actual complement operators, with inverse on the left of the index.",
                "First construct equivariant regular coordinates on U for J by normal-basis descent over the faithful actual center. The vector associated with the identity coordinate generates the J-coordinate blocks. Sum its actual translates over C to obtain a D-linear map from C -> S to W. The actual complement factorization and inertia stability show that its image contains every G-translate of U. This image is a k[G]-submodule; irreducibility makes it all of W. The original-D Clifford rank identity gives equality of domain and codomain dimensions, proving bijectivity. Reindexing the actual operator sum proves C-equivariance directly. Thus equality of dimensions is used only after constructing the map, proving surjectivity, and identifying its action.",
                "The equivalence uses the original Schur division ring throughout, without replacing it by the coefficient field or by a commutative division ring. The useful passage from group action to arithmetic is that a faithful action on the actual component center supplies fixed-field Galois descent and normal-basis coordinates. These coordinates are linear for the original D-action because the center operators commute with D. Clifford induction assembles them into full-complement regular coordinates; each complement coordinate has the same D-dimension, so its order, equal to N.index, divides the total dimension. Hall coprimality, Schur-Zassenhaus, Skolem-Noether, semilinear descent and normal bases are classical results or reused proofs. The formal integration constructs the actual centers, inertia components and equivariant maps together; it makes no global novelty claim."))));

    private static DocumentBlock Node(string name, Formula statement, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(name == "index_dvd_originalD_finrank" ?
                "original-d-frobenius-rank" : "original-d-frobenius-regular"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius." + name),
            H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Theorem);

    private static Formula RankStatement()
    {
        Formula k = F.Id("k"), g = F.Id("G"), n = F.Id("N"), rho = F.Id("rho");
        Formula w = App(Q("Representation", "asModule"), rho);
        Formula d = App(Q("Module", "End"), App(F.Id("MonoidAlgebra"), k, g), w);
        return Hypotheses(App(Q("Dvd", "dvd"), App(Q("Subgroup", "index"), n),
            App(Q("Module", "finrank"), d, w)));
    }

    private static Formula RegularStatement()
    {
        Formula k = F.Id("k"), g = F.Id("G"), n = F.Id("N"), rho = F.Id("rho");
        Formula c = F.Id("C"), s = F.Id("S"), e = F.Id("E"), v = F.Id("v"), x = F.Id("x");
        Formula w = App(Q("Representation", "asModule"), rho);
        Formula d = App(Q("Module", "End"), App(F.Id("MonoidAlgebra"), k, g), w);
        Formula act = App(Q("OriginalDCliffordCandidate", "originalDTranslate"), rho, F.Id("c"), v);
        Formula law = All("c", c, All("v", w, All("x", c,
            Eq(App(e, act, x), App(e, v, Mul(App(Q("Inv", "inv"), F.Id("c")), x))))));
        Formula result = Exists("C", App(F.Id("Subgroup"), g), And(
            App(Seq(Q("Subgroup", "IsComplement"), Apos), n, c),
            Exists("S", App(F.Id("Submodule"), d, w),
                Exists("E", App(F.Id("LinearEquiv"), App(Q("RingHom", "id"), d), w, Arr(c, s)), law))));
        return Hypotheses(result);
    }

    private static Formula Hypotheses(Formula result)
    {
        Formula k = F.Id("k"), g = F.Id("G"), v = F.Id("V"), n = F.Id("N"), rho = F.Id("rho");
        Formula z = F.Id("g"), x = F.Id("n");
        Formula restriction = App(Q("MonoidHom", "comp"), rho, App(Q("Subgroup", "subtype"), n));
        Formula fixedFree = All("g", g, Imp(Not(App(Q("Membership", "mem"), n, z)),
            All("n", n, Imp(Eq(App(App(Q("MulAut", "conjNormal"), z), x), x), Eq(x, D(1))))));
        result = All("hnt", Not(App(Q("Representation", "IsTrivial"), restriction)), result);
        result = All("hfix", fixedFree, result);
        result = Instance(App(Q("Representation", "IsIrreducible"), rho), result);
        result = Instance(App(Q("Module", "Finite"), k, v), result);
        result = All("rho", App(F.Id("Representation"), k, g, v), result);
        result = Instance(App(Q("Subgroup", "Normal"), n), result);
        result = All("N", App(F.Id("Subgroup"), g), result);
        result = Instance(App(F.Id("Module"), k, v), result);
        result = Instance(App(F.Id("AddCommGroup"), v), result);
        result = Instance(App(F.Id("Field"), k), result);
        result = Instance(App(F.Id("Finite"), g), result);
        result = Instance(App(F.Id("Group"), g), result);
        return All("k", TypeStar(), All("G", TypeStar(), All("V", TypeStar(), result)));
    }

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string n, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Exists(string n, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Not(Formula p) => Seq(Neg, Sp, Open, p, Close);
    private static Formula TypeStar() => Seq(F.Id("Type"), Star);
    private static Formula Instance(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
}
