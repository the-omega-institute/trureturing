using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GaloisVectorDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective descent for semilinear Galois vector spaces.", H("Effective descent for semilinear Galois vector spaces."),
        Blocks(
            Paragraph(Text("The invariant-generation method follows Qiuzhen-CFSG/CFSG, Theory/Representation/FiniteFieldSemilinearDisplacement/Descent.lean, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, Apache-2.0. The formulation with independent group, base-field, extension-field and carrier universes and the canonical tensor equivalence are the formal integration here. Basis extraction and base change use Mathlib. This is classical semilinear descent, with no claim of a new descent theorem.")),
            Describe.Lean(DescribeId.Create("galoisvectordescent-span-fixedpoints"), DeclarationHandle.Create("D5/S3/Factorization/Galois/GaloisVectorDescent.span_fixedPoints"), H("span fixedPoints"), StatementSource.FromAuthor(Disp(Span())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The fixed vectors span over the extension field. Twisted orbit sums are fixed, so a linear form vanishing on the fixed vectors gives a relation among distinct field automorphisms. Artin independence makes that form zero. No division by the group order or finite-dimensionality is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("galoisvectordescent-exists-invariant-basis"), DeclarationHandle.Create("D5/S3/Factorization/Galois/GaloisVectorDescent.exists_invariant_basis"), H("exists invariant basis"), StatementSource.FromAuthor(Disp(Basis())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Extracting a basis from the spanning fixed vectors gives a basis fixed pointwise by the group; its index type lies in the carrier universe."))), DescribeRole.Theorem),
            Paragraph(Math(Disp(Descent()))),
            Paragraph(Text("The canonical L-linear equivalence descentEquiv sends a tensor a tensor w to a times w. Its inverse is determined by the invariant basis. The K-module and scalar-tower structures in this formula are scalar restriction; they impose no new restriction on an L-vector space.")))));


    private static Formula Span() => Inputs(Eq(App(Q("Submodule", "span"), I("L"),
        App(Q("MulAction", "fixedPoints"), I("G"), I("V"))), Q("Top", "top")), false);
    private static Formula Basis() => Inputs(Ex("iota", Ty(), Ex("b", App(I("Basis"), I("iota"), I("L"), I("V")),
        All("g", I("G"), All("i", I("iota"), Eq(App(Q("HSMul", "hSMul"), I("g"), App(I("b"), I("i"))), App(I("b"), I("i"))))))), false);
    private static Formula Fixed() => App(Q("GaloisVectorDescent", "fixedSubmodule"), I("G"), I("K"), I("L"), I("V"));
    private static Formula Descent()
    {
        Formula tensor = App(Q("Algebra", "TensorProduct"), I("K"), I("L"), Fixed());
        Formula law = All("a", I("L"), All("w", Fixed(), Eq(
            App(Q("GaloisVectorDescent", "descentEquiv"), I("G"), I("K"), I("L"), I("V"),
                App(Q("TensorProduct", "tmul"), I("a"), I("w"))),
            App(Q("HSMul", "hSMul"), I("a"), App(Q("Subtype", "val"), I("w"))))));
        return Inputs(Seq(App(Q("GaloisVectorDescent", "descentEquiv"), I("G"), I("K"), I("L"), I("V")), Colon, App(I("LinearEquiv"), App(Q("RingHom", "id"), I("L")), tensor, I("V")), Comma, Sp, law), true);
    }
    private static Formula Inputs(Formula p, bool baseScalars)
    {
        if (baseScalars) { p = Inst(App(I("IsScalarTower"), I("K"), I("L"), I("V")), p); p = Inst(App(I("Module"), I("K"), I("V")), p); }
        p = Inst(App(I("SMulDistribClass"), I("G"), I("L"), I("V")), p);
        p = Inst(App(I("DistribMulAction"), I("G"), I("V")), p);
        p = Inst(App(I("Module"), I("L"), I("V")), p);
        p = Inst(App(I("AddCommGroup"), I("V")), p);
        p = Inst(App(I("IsGaloisGroup"), I("G"), I("K"), I("L")), p);
        p = Inst(App(I("MulSemiringAction"), I("G"), I("L")), p);
        p = Inst(App(I("Algebra"), I("K"), I("L")), p);
        p = Inst(App(I("Field"), I("L")), p); p = Inst(App(I("Field"), I("K")), p);
        p = Inst(App(I("Finite"), I("G")), p); p = Inst(App(I("Group"), I("G")), p);
        return All("G", Ty(), All("K", Ty(), All("L", Ty(), All("V", Ty(), p))));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);
}
