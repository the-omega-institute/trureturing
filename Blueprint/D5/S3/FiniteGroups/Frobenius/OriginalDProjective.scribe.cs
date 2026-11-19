using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDProjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projectivity of the actual original-D Frobenius module by coordinate sections and relative trace.",
        H("Original-D Frobenius projectivity"),
        Blocks(Describe.Lean(DescribeId.Create("original-d-frobenius-projective"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDProjective.projective_originalD"),
            H("Projectivity from the kernel order"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let k be any field, G a finite group, N a normal subgroup, and rho a finite-dimensional irreducible representation whose restriction to N is nontrivial. Suppose every conjugation by an element outside N fixes only the identity in N. If the image of |N| in k is a unit, then W = rho.asModule is projective over the actual group algebra k[G]. The field, group and carrier universes are independent.")),
                Paragraph(Text("Use exists_complement_originalD_regular to obtain the actual complement C, the D-submodule S of W and the equivariant coordinates E : W -> (C -> S), where D is literally Module.End k[G] W. Existing scalar-tower instances restrict E to the original field k. For a surjection f : P -> W, choose a k-linear section t and put j(z) = E^(-1)(delta_1(z)). Define s_C(v) = sum over c in C of c t(j(E(v)(c))). The coordinate law gives E(c j(z)) = delta_c(z), so f(s_C(v)) = v by coordinate reconstruction. Reindexing c by d^(-1)c proves s_C(d v) = d s_C(v). This constructs a section from regular coordinates without dividing by |C|.")),
                Paragraph(Text("For g in G set A_g(v) = g s_C(g^(-1)v). Complement equivariance proves A_(gc) = A_g, so the summand descends to the left-coset set G/C even when C is not normal. Sum the descended k-linear maps over this finite quotient. Left multiplication permutes G/C and proves that the sum T commutes with every G operator. The existing equivariantOfLinearOfComm interface makes T a k[G]-linear map. Every coset contributes v to f(T(v)), hence f(T(v)) = [G:C] v. The complement identity gives [G:C] = |N|. Multiplying T by the inverse of this scalar splits f. Applying this construction to the canonical free surjection proves projectivity without a Small assumption.")),
                Paragraph(Text("The characteristic boundary comes entirely from the last normalization: only |N| must be invertible in k. The proof imposes no invertibility condition on |C| or |G|, no normality of C, no commutativity of D and no new scalar-tower hypothesis. It asserts no converse in other characteristics. This formal integration uses the existing original-D regular-coordinate theorem, vector-space projectivity and the classical relative-trace argument; it makes no novelty claim and includes no separately formalized finite-field example."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = F.Id("k"), g = F.Id("G"), v = F.Id("V"), n = F.Id("N"), rho = F.Id("rho");
        Formula z = F.Id("g"), x = F.Id("n");
        Formula w = App(Q("Representation", "asModule"), rho);
        Formula result = App(Q("Module", "Projective"), App(F.Id("MonoidAlgebra"), k, g), w);
        Formula cast = Seq(Open, App(Q("Nat", "card"), n), Sp, Colon, Sp, k, Close);
        result = All("hunit", App(F.Id("IsUnit"), cast), result);
        Formula restriction = App(Q("MonoidHom", "comp"), rho, App(Q("Subgroup", "subtype"), n));
        result = All("hnt", Not(App(Q("Representation", "IsTrivial"), restriction)), result);
        Formula fixedFree = All("g", g, Imp(Not(App(Q("Membership", "mem"), n, z)),
            All("n", n, Imp(Eq(App(App(Q("MulAut", "conjNormal"), z), x), x), Eq(x, D(1))))));
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
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Not(Formula p) => Seq(Neg, Sp, Open, p, Close);
    private static Formula TypeStar() => Seq(F.Id("Type"), Star);
    private static Formula Instance(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
}
