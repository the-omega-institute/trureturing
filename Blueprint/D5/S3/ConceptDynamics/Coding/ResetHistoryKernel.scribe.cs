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

    private static Formula ProductEmbedding => Call("gapProductKernelEmbedding", I("q"), I("hq"), I("hqzero"));
    private static Formula ProductScope(Formula f) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("hq", Le(Num(2), I("q"))), B("hqzero", Lt(Num(0), I("q")))], f);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite alternating subgroups and their simultaneous finite-support product in the original Reset kernel.",
        H("Original dynamics and cyclic arithmetic"),
        Blocks(
            Entry("rho_time", "Original full-rho commutation",
                new Formula.BindMany(FormulaQuantifier.ForAll,
                    [B("q", I("Nat")), B("hq", Lt(Num(0), I("q"))),
                     B("h", Call("ResetFullAut", I("q"))), B("x", Call("Native", I("q")))],
                    Equal(Call("rho", I("q"), I("hq"), I("h"), Call("resetTheta", I("q"), I("x"))),
                        Call("resetTheta", I("q"), Call("rho", I("q"), I("hq"), I("h"), I("x"))))),
                "This existing owning argument applies the actual representation to the literal "
                + "fullAutSubgroup shift-commutation law and uses rho_unitShift. It is public for "
                + "ResetNativeUnitNormalForm's complete original-rho consumer.", DescribeRole.Theorem),
            Entry("centralizingMap_scalar", "The consumed general scalar argument",
                new Formula.BindMany(FormulaQuantifier.ForAll,
                    [B("q", I("Nat")), B("hq", Lt(Num(0), I("q"))),
                     B("A", Call("IntLinearEnd", Call("Native", I("q")))),
                     B("ht", Call("commutesWithForwardTime", I("q"), I("A"))),
                     B("b", Call("QF", I("q")))],
                    Equal(Call("centralizingMap", I("q"), I("hq"), I("A"), I("ht"), I("b")),
                        Call("multiply", I("b"),
                            Call("centralizingMap", I("q"), I("hq"), I("A"), I("ht"), Num(1))))),
                "commutesWithForwardTime(q,A) means forall x, A(resetTheta(q,x))=resetTheta(q,A(x)). "
                + "centralizingMap transports A by nativeIntEquiv and promotes it to Int[X]-linearity "
                + "with LinearMap.ofAEval. Polynomial-quotient surjectivity gives the scalar law. "
                + "The original chartMap and chartMap_scalar specialize this same owning argument "
                + "to actual rho. ResetNativeUnitNormalForm consumes it for both A and its inverse. "
                + "This generalized helper supplies no new component-unit classification.", DescribeRole.Theorem),
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
                DescribeRole.Theorem),
            Entry("FiniteGapAlternating", "A countable product with finite support",
                Typed(I("FiniteGapAlternating"), I("Type")),
                "This is Mathlib RestrictedProduct with n-th fiber Alt(Fin(2^(n+2))), "
                + "bottom subgroups, and Filter.cofinite. A tuple has finitely many "
                + "nonidentity coordinates, multiplied coordinatewise in their original "
                + "noncommutative groups. The coordinate n=0 is A4.", DescribeRole.Definition),
            Entry("gapProductKernelEmbedding", "Simultaneous action in the original kernel",
                ProductScope(Typed(ProductEmbedding, Call("MonoidHom", I("FiniteGapAlternating"),
                    Call("kernel", Call("rho", I("q"), I("hqzero")))))),
                "Use the actual signed edge b: (0,zeta)→(0,1), and a: (0,1)→(0,zeta). "
                + "With c_h the chain 0→1 and d_h the reset from 1, U=a c_zeta d_zeta "
                + "and V=c_one d_one c_zeta d_zeta are b-free loops at (0,1), of lengths "
                + "3 and 4. A bit is U^4 or V^3. Concatenating n+2 blocks and closing "
                + "with a gives d(n)=12(n+2)+1 edges from target(b) to source(b). "
                + "The first edges of the two blocks differ, so the codes are injective. "
                + "All edges are transported through originalEdge with their actual labels, "
                + "numbers and absolute signs. The chain requires q>=2.", DescribeRole.Definition),
            Entry("gapProductKernelEmbedding_injective", "Joint faithfulness on all original histories",
                ProductScope(Call("FunctionInjective", ProductEmbedding)),
                "SeparatorGapAction proves that overlapping interiors between consecutive "
                + "b edges have the same endpoints. It proves exact separator preservation, "
                + "both directions of eligibility invariance, and cross-length commutation "
                + "on arbitrary bilateral sequences. The legal seams use the distinct "
                + "source and target of b. Its finite-support homomorphism acts on ALL "
                + "History(ResetGraph q), commutes with the actual unit shift and has a real "
                + "continuous inverse. On a realized word b D(n,i) b, every other length "
                + "fixes the central data while coordinate n outputs D(n,g(n)(i)); this "
                + "determines every coordinate of the tuple. Noncoded gaps, extra q>2 "
                + "edges and arbitrary exterior tails are included. The original rho "
                + "has commuting images by the cyclic integer chart. Alternating factors "
                + "are killed as restrictions of these new symmetric actions, using "
                + "three-cycle commutators in Sym, including A4. Subgroup closure places "
                + "the finite product in the SAME rho kernel. The classical marker method "
                + "is discussed in Library/FiniteGroups/boylelindrudolph1988automorphism.md. "
                + "There is no q=1 claim, unrestricted infinite-product continuity, "
                + "publication novelty claim or classification of the whole kernel.", DescribeRole.Theorem))));
}
