using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetHistoryKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.";
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string n, Formula t) =>
        new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula f, bool hq0) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("k", I("Nat")), B("hq", Le(Num(2), I("q"))),
         B("hk", Le(Num(2), I("k"))),
         .. (hq0 ? new[] { B("hq0", Lt(Num(0), I("q"))) } : [])], f);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Typed(Formula a, Formula b) => Seq(a, Colon, b);
    private static Formula N => Call("Fin", new Formula.Power(Num(2), I("k")));
    private static Formula Emb => Call("alternatingKernelEmbedding", I("q"), I("k"),
        I("hq"), I("hk"), I("hq0"));
    private static DocumentBlock Entry(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Large finite nonabelian subgroups in the original Reset beam representation kernel.",
        H("Original dynamics and cyclic arithmetic"),
        Blocks(
            Paragraph(Text(
                "The original rho acts on DimensionGroup(resetMatrix q) by actual beam "
                + "pushforward. Every full history automorphism commutes with UNIT shift; "
                + "rho_unitShift identifies its native image with forward resetTheta. "
                + "nativePolynomialEquiv then makes the transported image polynomial-linear "
                + "on QF=Z[X]/(F q). Its value at 1 determines it as multiplication by that "
                + "value, so actual image maps commute. No ring is installed on Native.")),
            Paragraph(Text(
                "The live nonbinding input is MarkerPermutationAction's faithful guarded "
                + "action on ALL original Reset histories. Its marker and eligibility invariance "
                + "are indispensable to the inverse and group law. Reindexing, cyclicity, "
                + "centralizer commutativity and commutator transport are consumed library "
                + "applications, not separate mathematical contributions. The classical marker "
                + "method is attributed in the owning MarkerPermutationAction Scribe and the "
                + "Boyle–Lind–Rudolph library note.")),
            Entry("symmetricAction", "The prescribed finite symmetric group action",
                All(Typed(Call("symmetricAction", I("q"), I("k"), I("hq"), I("hk")),
                    Call("MonoidHom", Call("Perm", N), Call("ResetFullAut", I("q")))), false),
                "Fin(2^k) is reindexed by the existing cardinal equivalence with Fin k→Bool. "
                + "This transports the actual resetAction without changing any graph, "
                + "history, shift, topology or representation. Its radius is 12k+5.",
                DescribeRole.Definition),
            Entry("alternatingKernelEmbedding", "Alternating permutations land in the actual kernel",
                All(Typed(Emb, Call("MonoidHom", Call("alternatingGroup", N),
                    Call("kernel", Call("rho", I("q"), I("hq0"))))), true),
                "The hom restricts symmetricAction and codRestricts to (rho q hq0).ker. "
                + "Every three-cycle is conjugate to its square in Sym, hence a commutator "
                + "by mem_commutatorSet_of_isConj_sq. closure_three_cycles_eq_alternating "
                + "and abelian rho image kill the entire alternating group. This includes "
                + "k=2 and A4; it does not assume A4 perfect or use a cardinal>=5 theorem.",
                DescribeRole.Definition),
            Entry("alternatingKernelEmbedding_injective", "Uniform original-kernel injectivity",
                All(Call("FunctionInjective", Emb), true),
                "The injectivity is inherited from the genuine original-history action, "
                + "whose guarded words are realized by existing positive-word extension. "
                + "hq0 can be any proof of 0<q, which follows from q>=2. For k>=2 the "
                + "alternating groups are nonabelian, including A4, and their factorial "
                + "orders are unbounded as k grows. No cross-k compatibility, complete "
                + "kernel classification or locally finite whole-kernel conclusion is claimed.",
                DescribeRole.Theorem))));
}
