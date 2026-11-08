using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDRegularActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal-basis coordinates for covariant field operators over an independent division ring.",
        H("Descent with the original division ring"),
        Blocks(
            Node("normalMap_bijective", "original-d-normal-map", Bijective(), DescribeRole.Theorem,
                "Let F/K be a finite Galois extension, D an arbitrary division ring, and U a left D-module. Let a : F -> End_D(U) be a unital ring map and tau : Gal(F/K) -> End_D(U) a monoid map satisfying tau(g)a(x) = a(g(x))tau(g). The common fixed vectors form a D-submodule S. For a normal basis b of F/K, the D-linear map f -> sum_g a(b(g))f(g) from Gal(F/K) -> S to U is bijective.",
                "The field operators install the F-module structure on U, while covariance gives semilinearity of the Galois action. Galois vector descent identifies U with F tensor_K S. The tensor-basis equivalence for a normal basis identifies that tensor product with the function space. Comparing the composite with the displayed sum proves bijectivity. Its D-linearity follows from the D-linearity of the actual operators a(x). The descent supplier is GaloisVectorDescent, attributed to Qiuzhen-CFSG/CFSG, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, under Apache-2.0; normal bases and tensor-basis equivalences are from Mathlib."),
            Node("regularEquiv", "original-d-regular-equivalence", Equivalence(), DescribeRole.Definition,
                "The inverse of the normal-basis sum map gives a D-linear equivalence from U to Gal(F/K) -> S. The division ring D has no required embedding of K or F and is not required to be commutative. The universes of K, F, D and U are independent."),
            Node("regularEquiv_apply_action", "original-d-regular-action", ActionLaw(), DescribeRole.Theorem,
                "These coordinates intertwine the actual operators tau(h) with left translation: E(tau(h)u)(g) = E(u)(h^(-1)g). Covariance sends the normal-basis vector indexed by g to the one indexed by hg, and every coordinate value is fixed by tau. Reindexing the sum by left multiplication proves the law; inverting the bijective sum map gives the stated formula."))));

    private static DocumentBlock Node(string name, string id, Formula statement,
        DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction." + name),
            H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), role);

    private static Formula Gal() => App(F.Id("AlgEquiv"), F.Id("K"), F.Id("F"), F.Id("F"));
    private static Formula Fixed() => App(Q("FrobeniusOriginalD.RegularAction", "fixed"), F.Id("tau"));
    private static Formula Map() => App(Q("FrobeniusOriginalD.RegularAction", "normalMap"),
        F.Id("a"), F.Id("tau"));
    private static Formula E() => App(Q("FrobeniusOriginalD.RegularAction", "regularEquiv"),
        F.Id("a"), F.Id("tau"), F.Id("cov"));
    private static Formula Bijective() => Inputs(App(Q("Function", "Bijective"), Map()));
    private static Formula Equivalence() => Inputs(App(F.Id("LinearEquiv"),
        App(Q("RingHom", "id"), F.Id("D")), F.Id("U"), new Formula.TypeArrow(Gal(), Fixed())));
    private static Formula ActionLaw() => Inputs(All("h", Gal(), All("u", F.Id("U"), All("g", Gal(),
        Eq(App(E(), App(F.Id("tau"), F.Id("h"), F.Id("u")), F.Id("g")),
            App(E(), F.Id("u"), Mul(App(Q("Inv", "inv"), F.Id("h")), F.Id("g"))))))));

    private static Formula Inputs(Formula result)
    {
        Formula k = F.Id("K"), f = F.Id("F"), d = F.Id("D"), u = F.Id("U");
        Formula a = F.Id("a"), tau = F.Id("tau"), g = F.Id("g"), x = F.Id("x");
        Formula end = App(Q("Module", "End"), d, u);
        Formula cov = All("g", Gal(), All("x", f,
            Eq(Mul(App(tau, g), App(a, x)), Mul(App(a, App(g, x)), App(tau, g)))));
        result = All("cov", cov, result);
        result = All("tau", App(F.Id("MonoidHom"), Gal(), end), result);
        result = All("a", App(F.Id("RingHom"), f, end), result);
        result = Instance(App(F.Id("Module"), d, u), result);
        result = Instance(App(F.Id("AddCommGroup"), u), result);
        result = Instance(App(F.Id("DivisionRing"), d), result);
        result = Instance(App(F.Id("IsGalois"), k, f), result);
        result = Instance(App(Q("Module", "Finite"), k, f), result);
        result = Instance(App(F.Id("Algebra"), k, f), result);
        result = Instance(App(F.Id("Field"), f), result);
        result = Instance(App(F.Id("Field"), k), result);
        return All("K", TypeStar(), All("F", TypeStar(), All("D", TypeStar(), All("U", TypeStar(), result))));
    }

    private static Formula Q(string owner, string name)
    {
        Formula result = Seq(Operatorname, Grp(F.Id(owner.Split('.')[0])));
        foreach (string part in owner.Split('.').Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return Seq(result, Dot, Operatorname, Grp(F.Id(name)));
    }
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string n, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Instance(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula TypeStar() => Seq(F.Id("Type"), Star);
}
