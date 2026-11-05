using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanInfiniteFieldRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An associative commutative nilpotent rational algebra of dimension three "
            + "has a two-dimensional subspace on which every nonzero vector has nonzero square.",
        H("The infinite-field branch of Bergman's Question 19 for Question 16"),
        Blocks(
            Node("common-nilpotence", "CommonNilpotent", "One common vanishing product length",
                CommonFormula(), AssessedProvenance.FromRepo(Source),
                "LinearMap(F,A,B) denotes an F-linear map from A to B. Thus the curried "
                    + "type LinearMap(F,R,LinearMap(F,R,R)) supplies actual F-bilinear "
                    + "multiplication. Type* permits arbitrary universes. The implicit scalar "
                    + "and carrier arguments are displayed explicitly. foldr(mu,z,xs) means "
                    + "xs.foldr (fun x y => mu x y) z, with the terminal factor z included. "
                    + "A list of length k therefore gives k+1 factors; k=0 permits only the "
                    + "zero algebra. The quantifier selects one length for every list and "
                    + "terminal factor. Under associativity this is the usual global "
                    + "nilpotence condition, equivalently vanishing of the corresponding product-span.",
                DescribeRole.Definition),
            Node("infinite-field-assertion", "claim", "The complete affirmative field assertion",
                ClaimFormula(), AssessedProvenance.FromLiterature(Source),
                "Bergman's Question 16 asks for the dimension bound over algebraically "
                    + "closed fields. Question 19 explicitly asks whether that assumption "
                    + "can be dropped, or weakened to an infinite field. The displayed closed "
                    + "claim is the infinite-field alternative, with associativity and "
                    + "commutativity retained. The source's Convention 2 assumes associative "
                    + "algebras, without requiring an identity. No identity is introduced here. "
                    + "Every dimension and linearity condition uses F. The subspace V is a "
                    + "Submodule, and finrank(F,V) is the dimension of its subtype. "
                    + "Natural subtraction is truncated; for the required positive n, "
                    + "replicate(n-1,v) followed by v has exactly n factors, including n=1. "
                    + "The assertion quantifies over all nonzero vectors, all positive "
                    + "exponents, all finite-dimensional carriers and all infinite fields "
                    + "in Type, without an ordering or characteristic hypothesis.",
                DescribeRole.Definition),
            Node("annihilating-product", "product", "A bilinear quadratic multiplication",
                ProductFormula(), AssessedProvenance.FromRepo(Source),
                "Use the ordinary product vector space (F x F) x F, with its coordinatewise "
                    + "addition and scalar multiplication, for any field F. The displayed "
                    + "type is a curried linear map, constructed by LinearMap.mk2; the four "
                    + "additivity and scalar-linearity obligations are proved in its definition. "
                    + "Only the first two coordinates enter the scalar product. Every output "
                    + "lies on the third-coordinate line, which annihilates the whole algebra. "
                    + "Consequently both bracketings of every triple product are zero, "
                    + "and symmetry of the scalar product gives commutativity. These laws "
                    + "are verified for the rational model in the proof of result.",
                DescribeRole.Definition),
            Node("model-subspace", "modelSubspace", "The coordinate plane as a linear range",
                SubspaceFormula(), AssessedProvenance.FromRepo(Source),
                "The map inl(F,F x F,F) is the linear injection w maps to (w,0). "
                    + "Its range is precisely the coordinate plane of vectors ((a,b),0). "
                    + "This is a genuine linear subspace, rather than an arbitrary set "
                    + "of individually selected vectors. Injectivity and the dimension "
                    + "of a linear range give its dimension two over the same F.",
                DescribeRole.Definition),
            Node("field-branch-refuted", "result", "The infinite-field dimension bound fails",
                Disp(new Formula.Not(F.Id("claim"))), AssessedProvenance.FromRepo(Source),
                "Take F=Q, R=(Q x Q) x Q, V=modelSubspace(Q), and n=2. The field Q is "
                    + "infinite and the ambient dimension is three. Every product of three "
                    + "elements is zero, witnessed by k=2 in CommonNilpotent. For a vector "
                    + "((a,b),0) in V its square is ((0,0),a*a+b*b). The ordered-field "
                    + "identity mul_self_add_mul_self_eq_zero implies that this vanishes "
                    + "only when a=b=0, so every nonzero vector in V has nonzero square. "
                    + "The dimension of V is two, and the asserted bound would read "
                    + "2*2 <= 3, which is false. Associativity, commutativity, common "
                    + "nilpotence, nonannihilation and both dimensions are established "
                    + "inside the proof; none is assumed as a countermodel premise. "
                    + "Since Q is infinite, this also rules out the alternative with no "
                    + "field restriction. It does not settle Question 16 over algebraically "
                    + "closed fields, the noncommutative branches of Question 19, or Eggert's conjecture.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bergman-question19-question16-field-condition"),
                    ResolutionKind.Refuted)),
            Paragraph(Text(
                "Bergman's Example 20 already uses an inner product and graded pieces "
                    + "of dimensions d,1,d to obtain a nonassociative real cubing example. "
                    + "The quadratic mechanism here is its degree-one/degree-two truncation: "
                    + "the scalar output is made annihilating, so every triple product "
                    + "vanishes and associativity holds. The model uses rational coordinates "
                    + "and squares at n=2, rather than the source's nonassociative cubing "
                    + "at n=3. Credit for the inner-product mechanism belongs to Bergman. "
                    + "The bounded literature screen located no exact settlement of this "
                    + "associative field branch; worldwide priority remains unverified.")))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("bergman-field-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Scalar => F.Id("F");
    private static Formula Carrier => F.Id("R");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Type => Named("Type");
    private static Formula TypeStar => Seq(Type, Caret, Grp(Star));
    private static Formula Triple => PairType(PairType(Scalar, Scalar), Scalar);
    private static Formula Bilinear(Formula r) =>
        Call("LinearMap", Scalar, r, Call("LinearMap", Scalar, r, r));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Tuple(params Formula[] items)
    {
        var content = new System.Collections.Generic.List<Formula>();
        foreach (var item in items)
        {
            if (content.Count != 0) content.Add(Comma);
            content.Add(item);
        }
        return Par(Seq([.. content]));
    }
    private static Formula PairType(Formula a, Formula b) => Par(Seq(a, Sp, Times, Sp, b));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Typed(F.Id(name), type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Typed(F.Id(name), type)), Comma, Sp, body);
    private static Formula ForMu(Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Typed(Mu, type)), Comma, Sp, body);
    private static Formula ApplyMu(Formula x, Formula y) => Seq(Mu, Tuple(x, y));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffRel(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fold(Formula xs, Formula z) => Call("foldr", Mu, z, xs);
    private static Formula AmbientInstances(Formula body) => Seq(
        Instance("AddCommGroup", Carrier), Instance("Module", Scalar, Carrier), body);
    private static Formula FieldBinder(Formula body, bool small = false) =>
        All("F", small ? Type : TypeStar, Seq(Instance("Field", Scalar), body));

    private static Formula CommonFormula()
    {
        var k = F.Id("k");
        var xs = F.Id("xs");
        var z = F.Id("z");
        var body = Some("k", Nat, All("xs", Call("List", Carrier), All("z", Carrier,
            Imp(Eqn(Call("length", xs), k), Eqn(Fold(xs, z), D(0))))));
        return Disp(FieldBinder(All("R", TypeStar, AmbientInstances(ForMu(Bilinear(Carrier),
            IffRel(Typed(Call("CommonNilpotent", Scalar, Carrier, Mu), Named("Prop")), body))))));
    }

    private static Formula ClaimFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var v = F.Id("v"); var space = F.Id("V"); var n = F.Id("n");
        var assoc = All("x", Carrier, All("y", Carrier, All("z", Carrier,
            Eqn(ApplyMu(ApplyMu(x, y), z), ApplyMu(x, ApplyMu(y, z))))));
        var comm = All("x", Carrier, All("y", Carrier, Eqn(ApplyMu(x, y), ApplyMu(y, x))));
        var powers = All("v", Carrier,
            Imp(new Formula.Relation(v, FormulaRelationOperator.MemberOf, space),
                Imp(Ne(v, D(0)), Ne(Fold(Call("replicate", MinusOf(n, D(1)), v), v), D(0)))));
        var bound = LeRel(TimesOf(n, Call("finrank", Scalar, space)),
            Call("finrank", Scalar, Carrier));
        var body = Imp(assoc, Imp(comm, Imp(Call("CommonNilpotent", Scalar, Carrier, Mu),
            All("V", Call("Submodule", Scalar, Carrier), All("n", Nat,
                Imp(LtRel(D(0), n), Imp(powers, bound)))))));
        return Disp(IffRel(Typed(F.Id("claim"), Named("Prop")),
            FieldBinder(Seq(Instance("Infinite", Scalar), All("R", Type,
                AmbientInstances(Seq(Instance("FiniteDimensional", Scalar, Carrier),
                    ForMu(Bilinear(Carrier), body))))), small: true)));
    }

    private static Formula ProductFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var d = F.Id("d"); var e = F.Id("e"); var f = F.Id("f");
        var equation = Eqn(Call("product", Scalar, Tuple(Tuple(a, b), c), Tuple(Tuple(d, e), f)),
            Tuple(Tuple(D(0), D(0)), PlusOf(TimesOf(a, d), TimesOf(b, e))));
        foreach (var name in new[] { "f", "e", "d", "c", "b", "a" })
            equation = All(name, Scalar, equation);
        return Disp(FieldBinder(Seq(Typed(Call("product", Scalar), Bilinear(Triple)),
            Comma, Sp, equation)));
    }

    private static Formula SubspaceFormula() => Disp(FieldBinder(Seq(
        Typed(Call("modelSubspace", Scalar), Call("Submodule", Scalar, Triple)), Comma, Sp,
        Eqn(Call("modelSubspace", Scalar), Call("range", Call("inl", Scalar,
            PairType(Scalar, Scalar), Scalar))))));
}
