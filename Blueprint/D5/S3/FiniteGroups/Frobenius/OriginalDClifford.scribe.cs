using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDCliffordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original D Clifford", H("OriginalDClifford"), Blocks(
            Paragraph(Text("Constituent conjugacy is reused from CliffordConstituents; direct sums and isotypic decomposition are from Mathlib. The integration retains the original endomorphism ring and constructs component transport and the inertia-coset correspondence. It requires no commutative replacement of D or additional decomposition assumption.")),
            Paragraph(Text("Fully invariant isotypic submodules are stable under every commuting scalar action. The direct-sum map is consequently linear over the independent commuting scalar semiring.")),
            Paragraph(Text("A semilinear automorphism of a module transports its isotypic component to the component of the transported submodule. Transport the defining family and use the inverse for the reverse inclusion.")),
            Paragraph(Text("The actual group operator is linear over the original Schur division ring, because endomorphisms of the group-algebra module commute with it. Semilinear transport identifies its image component.")),
            Paragraph(Text("The actual inertia subgroup is the stabilizer of the chosen isotypic component. Its cosets correspond bijectively to the components. The resulting product equivalence is linear over D = Module.End k[G] rho.asModule. Taking dimensions gives the original-D Clifford product formula, with independent field, group and carrier universes.")),
            Paragraph(Text("The ambient group need not be finite for this formula: finite dimension and irreducibility give finitely many isotypic components and hence finite actual inertia index. The component and inertia are constructed, not supplied as additional hypotheses. All field, group and carrier universes are independent.")),
            Describe.Lean(DescribeId.Create("originaldclifford-originald-finrank-independent-universes"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDClifford.originalD_finrank_independent_universes"), H("originalD finrank independent universes"), StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original endomorphism ring acts on each transported isotypic component, and dimensions multiply by the actual inertia index."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = I("k"), g = I("G"), v = I("V"), n = I("N"), rho = I("rho"), sigma = I("sigma"), hs = I("hsigma");
        Formula w = App(Q("Representation", "asModule"), rho);
        Formula d = App(Q("Module", "End"), App(I("MonoidAlgebra"), k, g), w);
        Formula inertia = App(Q("CliffordDecomposition.Representation", "originalDActualInertia"), rho, sigma, hs);
        Formula component = App(Q("OriginalDCliffordCandidate", "originalDBaseComponent"), rho, sigma, hs);
        Formula p = Eq(App(Q("Module", "finrank"), d, w), Mul(App(Q("Subgroup", "index"), inertia), App(Q("Module", "finrank"), d, component)));
        p = All("hsigma", App(I("IsAtom"), sigma), p);
        Formula res = App(Q("MonoidHom", "comp"), rho, App(Q("Subgroup", "subtype"), n));
        p = All("sigma", App(I("Subrepresentation"), res), p);
        p = Inst(App(Q("Representation", "IsIrreducible"), rho), p);
        p = Inst(App(Q("Module", "Finite"), k, v), p);
        p = All("rho", App(I("Representation"), k, g, v), p);
        p = Inst(App(Q("Subgroup", "Normal"), n), p); p = All("N", App(I("Subgroup"), g), p);
        p = Inst(App(I("Module"), k, v), p); p = Inst(App(I("AddCommGroup"), v), p);
        p = Inst(App(I("Group"), g), p); p = Inst(App(I("Field"), k), p);
        return All("k", Ty(), All("G", Ty(), All("V", Ty(), p)));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string owner, string name)
    {
        Formula result = Seq(Operatorname, Grp(I(owner.Split('.')[0])));
        foreach (string part in owner.Split('.').Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(I(part)));
        return Seq(result, Dot, Operatorname, Grp(I(name)));
    }
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);
}
