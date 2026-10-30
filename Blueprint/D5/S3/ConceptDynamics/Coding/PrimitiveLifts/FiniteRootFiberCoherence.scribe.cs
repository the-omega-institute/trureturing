using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class FiniteRootFiberCoherenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence."
            + "finite_root_fibers_rational_coherence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under finite positive-degree root fibers, independent roots at every positive degree "
            + "are equivalent to a genuine monoid homomorphism from Multiplicative Q to H "
            + "with phi(Multiplicative.ofAdd(1:Q))=h.",
        H("Finite Root Fiber Coherence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-root-fibers-rational-coherence"),
            DeclarationHandle.Create(Declaration),
            H("Under finite positive-degree root fibers, independent roots at every positive degree "
                + "are equivalent to rational coherence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary group H, fix h and assume that every positive-degree "
                        + "fiber {b | b^n=h} is finite. The existence of a root in every positive "
                        + "degree is equivalent to a monoid homomorphism from Multiplicative Q to H "
                        + "with phi(Multiplicative.ofAdd(1:Q))=h. In the formula, ofAdd(q) denotes "
                        + "Multiplicative.ofAdd(q:Q), so ofAdd(1) is additive rational one; "
                        + "the multiplicative identity is ofAdd(0). No commutativity, divisibility, uniqueness, "
                        + "surjectivity, or topology hypothesis is used.")),
                Paragraph(Text(
                    "The forward implication is the compactness step. Positive degrees are ordered "
                        + "by divisibility, with common upper bound given by multiplication. The "
                        + "fiber at m maps to the fiber at n for n dividing m by b -> b^(m/n). "
                        + "Mathlib's finite inverse-system section theorem supplies compatible roots "
                        + "without requiring any bonding map to be onto.")),
                Paragraph(Text(
                    "For q=a/d define F(q)=b_d^a, with integer exponent. To prove F(q+r)=F(q)F(r), "
                        + "use the single root at d*e*f, where d,e,f are the denominators of q, r, "
                        + "and q+r. Every term is then an integer power of that same group element. "
                        + "Rat.add_num_den' supplies the exponent identity, so no commutation between "
                        + "different group elements is needed. The reverse implication evaluates the "
                        + "homomorphism at Multiplicative.ofAdd(1/n:Q) and uses map_pow.")),
                Paragraph(Text(
                    "The theorem asserts existence only. Finite fibers do not imply uniqueness of "
                        + "the resulting homomorphism.")),
                Paragraph(Text(
                    "The same root system and rational_action_of_coherent_roots also apply to a "
                        + "Hausdorff topological group H when every actual root set "
                        + "R_n(h)={x in H | x^n=h} is compact for every n>0. Roots exist in all positive "
                        + "degrees if and only if an algebraic monoid homomorphism phi:Multiplicative Q -> H "
                        + "sends Multiplicative.ofAdd(1:Q) to h. Give each root set its subspace topology "
                        + "and use the continuous power maps R_m(h) -> R_n(h), x -> x^(m/n), for n dividing m. "
                        + "Under the root-existence hypothesis these form a cofiltered system of nonempty "
                        + "compact Hausdorff spaces. Mathlib's "
                        + "TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system supplies compatible "
                        + "roots without requiring onto transition maps. The common cyclic denominator "
                        + "calculation above proves the homomorphism law even for noncommutative H; "
                        + "the converse again uses map_pow.")),
                Paragraph(Text(
                    "This composition of existing results connects the finite theorem to "
                        + "CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom: finite fibers "
                        + "are compact in the discrete group topology, while in a compact Hausdorff group "
                        + "each R_n(h) is closed as the inverse image of {h} under a continuous power map, "
                        + "and hence compact. The compact-root application requires neither finite root "
                        + "sets nor a compact ambient group. Its conclusion is algebraic existence only; "
                        + "it asserts no continuity or uniqueness of the homomorphism, no necessity of "
                        + "root-set compactness, and no literature novelty."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula h = F.Id("h");
        Formula group = F.Id("H");
        Formula positiveRoots = Call("positiveRootExistence", group, h);
        Formula finiteFibers = Call("finiteRootFibers", group, h);
        Formula rationals = Seq(Mathbb, Grp(F.Id("Q")));
        Formula actionType = Call("MonoidHom",
            Call("Multiplicative", rationals), group);
        Formula phi = F.Id("phi");
        Formula action = Exists("phi", actionType,
            Equal(Call("value", phi, Call("ofAdd", D(1))), h));
        Formula equivalence = new Formula.Logic(
            positiveRoots, FormulaLogicOperator.Iff, action);
        Formula hClause = new Formula.TypeArrow(finiteFibers, equivalence);
        Formula quantifiedH = All("h", group, hClause);
        Formula groupClause = new Formula.TypeArrow(Call("Group", group), quantifiedH);
        return Disp(All("H", F.Id("Typeu"), groupClause));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
}
