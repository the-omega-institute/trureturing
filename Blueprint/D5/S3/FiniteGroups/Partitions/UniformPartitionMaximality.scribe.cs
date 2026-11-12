using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Partitions;

internal sealed class UniformPartitionMaximalityDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Inst(Formula t, Formula b) =>
        Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Product(Formula k, Formula l) => Call("Product", k, l);
    private static Formula PermProduct(Formula k, Formula l) => Call("Perm", Product(k, l));
    private static Formula Aut(Formula k, Formula l) => Call("Aut", k, l);
    private static Formula Singleton(Formula x) => new Formula.SetLiteral([x]);
    private static Formula Scope(Formula b) =>
        All("K", V("Typeu"), All("L", V("Typev"), b));
    private static Formula FiniteBoth(Formula b) =>
        Inst(Call("Finite", V("K")), Inst(Call("Finite", V("L")), b));
    private static Formula FiniteNontrivial(Formula b) =>
        Inst(Call("Finite", V("K")), Inst(Call("Finite", V("L")),
            Inst(Call("Nontrivial", V("K")), Inst(Call("Nontrivial", V("L")), b))));
    private static Formula Top(Formula k, Formula l) =>
        Call("top", Call("Subgroup", PermProduct(k, l)));

    private static DocumentBlock.Describe Desc(string name, string title, Formula f,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("uniform-partition-maximality-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Partitions/UniformPartitionMaximality." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var k = V("K");
        var l = V("L");
        var aut = Aut(k, l);
        var q = V("q");
        var perm = PermProduct(k, l);
        var relation = Call("Set", aut);
        var generated = Call("closure", Call("union", relation, Singleton(q)));
        var qOutside = new Formula.Not(Mem(q, aut));
        var isCoatom = Scope(FiniteNontrivial(Call("IsCoatom", aut)));
        var closure = Scope(FiniteBoth(All("q", perm, Imp(qOutside, Eq(generated, Top(k, l))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "For finite nontrivial K and L, the uniform-partition automorphism subgroup is maximal in the full symmetric group on K times L.",
            H("Maximality of Uniform Partition Symmetries"), Blocks(
                Paragraph(Text("The relation is equality of first coordinates on K times L. "
                    + "Aut is the full subgroup preserving and reflecting that relation. "
                    + "When K and L are finite and nontrivial, it is a coatom: adjoining any "
                    + "permutation outside Aut generates the whole symmetric group.")),
                Desc("isCoatom_aut", "The uniform partition subgroup is a coatom", isCoatom,
                    "A same-block transposition lies in Aut. If a subgroup contains Aut and a permutation q outside it, q or q inverse sends a same-block pair across blocks. Conjugating the corresponding same-block swap and transporting it across blocks yields every transposition. All transpositions generate the full symmetric group on a finite carrier; on an infinite carrier they generate only the finite-support permutations, while the full symmetric group also contains permutations of infinite support. The proof keeps both finite and nontrivial hypotheses, including the size-two boundary."),
                Desc("closure_aut_union_singleton", "Adjoining any outside permutation generates the full group", closure,
                    "For finite K and L, every q outside Aut satisfies closure (Aut union {q}) = top. The argument uses q or q inverse to expose a cross-block image, then conjugates one within-block swap and transports it across arbitrary ordered cross-block pairs. Generation uses all of Aut together with q. No nontriviality assumption is needed for this implication; when Aut is already the full group, there is no outside q."),
                Paragraph(Text("For every n, a : Nat with n > 0, put g = gcd(n, a), ell = n/g and "
                    + "W = ZeroFamilyAut n a, a subgroup of Perm (Fin n). In the owning module "
                    + "D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries, the public APIs "
                    + "residueChart, sameCycle_iff_chart and zeroFamilyAut_eq_orbitAut identify the actual "
                    + "ambient subgroup, by conjugation through residueChart, with Aut (Fin g) (Fin ell), "
                    + "the first-coordinate partition subgroup. The abstract zeroFamilyEquiv alone does "
                    + "not identify this embedding. Transporting the results above therefore gives: "
                    + "if 1 < g < n, W is a coatom in the full symmetric group on Fin n; for every "
                    + "positive n and every q outside W, closure (W union {q}) = top. This generation "
                    + "uses all of W together with q. W stabilizes the whole family of actual zero "
                    + "subsets setwise and may exchange individual zero subsets. These are consequences "
                    + "of the cited arithmetic API and the generic theorems, with no additional "
                    + "canonical theorem. The outside-q implication retains a = 0, n = 1 and ell = 1; "
                    + "in these cases W is the full group and its outside-q premise is empty."))
            ), []));
    }
}
