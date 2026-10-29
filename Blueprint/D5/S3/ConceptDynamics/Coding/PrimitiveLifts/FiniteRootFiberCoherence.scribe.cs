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
        "Finite root fibers in a group, or compact root fibers in a Hausdorff topological group, "
            + "turn independent positive roots into a monoid homomorphism from Multiplicative Q to H "
            + "with phi(Multiplicative.ofAdd(1:Q))=h.",
        H("Finite and Compact Root Fiber Coherence"),
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
                        + "the resulting homomorphism."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-root-fibers-rational-coherence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence."
                        + "compact_root_fibers_rational_coherence"),
                H("Compact root spaces suffice for rational coherence"),
                StatementSource.FromAuthor(CompactTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a group with a topology making multiplication and inversion continuous, "
                            + "and assume that this topology is Hausdorff. Fix h in H. For every natural "
                            + "n>0 assume IsCompact {x in H | x^n=h}, using the actual topology of H. "
                            + "In the formula rootFiber(H,h,n) denotes exactly this set. Then roots in "
                            + "every positive degree exist if and only if there is an algebraic monoid "
                            + "homomorphism phi:Multiplicative Q -> H with phi(Multiplicative.ofAdd(1:Q))=h. "
                            + "The value is at additive rational one; ofAdd(0) is the multiplicative identity. "
                            + "All positive degrees, including n=1, are covered. The degree-one root space "
                            + "is the singleton {h}. The ambient group need not be compact, the root "
                            + "spaces need not be finite, and H need not be commutative.")),
                    Paragraph(Text(
                        "Use the same positive degrees ordered by divisibility and the same maps "
                            + "R_m(h) -> R_n(h), x -> x^(m/n), for n dividing m. Positive powers are "
                            + "continuous, so these actual root subspaces form a cofiltered system of "
                            + "nonempty compact Hausdorff spaces. Mathlib's "
                            + "TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system gives a compatible "
                            + "root in each degree. No transition map is required to be onto. "
                            + "The rational construction is the same as above: pass to a common cyclic "
                            + "denominator to prove the full homomorphism law. Conversely, phi(ofAdd(1/n)) "
                            + "is an n-th root of h by map_pow.")),
                    Paragraph(Text(
                        "The finite-root-fiber theorem is recovered by assigning the discrete topology "
                            + "to its arbitrary group: this is a Hausdorff group topology and finite "
                            + "root sets are compact. The compact ambient-group theorem "
                            + "CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom is also "
                            + "a specialization: each root set is the inverse image of the closed "
                            + "singleton {h} under a continuous power map, hence is closed and compact. "
                            + "Thus compact root spaces connect both existing results. This uses the "
                            + "classical compact inverse-limit principle and makes no literature novelty claim.")),
                    Paragraph(Text(
                        "The conclusion supplies existence of an algebraic homomorphism. It asserts "
                            + "neither continuity nor uniqueness, does not extend every prescribed root, "
                            + "and does not assert that compactness of the root spaces is necessary. "
                            + "The dyadic-solenoid rational-time application is already described in "
                            + "DyadicRootFiberArithmetic."))),
                DescribeRole.Theorem))));

    private static Formula CompactTheoremFormula()
    {
        Formula group = F.Id("H");
        Formula h = F.Id("h");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        Formula compactFibers = All("n", naturals,
            new Formula.TypeArrow(positive, Call("IsCompact", Call("rootFiber", group, h, n))));
        Formula roots = All("n", naturals,
            new Formula.TypeArrow(positive, Exists("x", group, Equal(Seq(x, Caret, Grp(n)), h))));
        Formula rationals = Seq(Mathbb, Grp(F.Id("Q")));
        Formula actionType = Call("MonoidHom", Call("Multiplicative", rationals), group);
        Formula action = Exists("phi", actionType,
            Equal(Call("value", F.Id("phi"), Call("ofAdd", D(1))), h));
        Formula body = All("h", group, new Formula.TypeArrow(compactFibers,
            new Formula.Logic(roots, FormulaLogicOperator.Iff, action)));
        return Disp(All("H", F.Id("Typeu"), Seq(
            OpenBracket, Call("Group", group), CloseBracket,
            OpenBracket, Call("TopologicalSpace", group), CloseBracket,
            OpenBracket, Call("IsTopologicalGroup", group), CloseBracket,
            OpenBracket, Call("T2Space", group), CloseBracket, body)));
    }

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
