using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class EquicontinuousObservationPeriodDocument : IScribeDocumentDefinition
{
    private static Formula DType => F.Id("D");
    private static Formula A => F.Id("A");
    private static Formula T => F.Id("T");
    private static Formula q => F.Id("q");
    private static Formula n => F.Id("n");
    private static Formula x => F.Id("x");
    private static Formula M => F.Id("M");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Map(Formula s, Formula t) => Seq(s, Sp, Rightarrow, Sp, t);
    private static Formula All(Formula v, Formula t) => Seq(Forall, Sp, v, Colon, Sp, t, Comma);
    private static Formula Hyp(Formula p) => Seq(p, Sp, Rightarrow);
    private static Formula Inst(string name, Formula t) =>
        Seq(Grp(), OpenBracket, Call(name, t), CloseBracket);
    private static Formula Statement => Disp(new Formula.Aligned([
        All(DType, F.Id("Type")), All(A, F.Id("Type")),
        Inst("UniformSpace", DType), Inst("CompactSpace", DType),
        Inst("TopologicalSpace", A), Inst("DiscreteTopology", A),
        All(T, Map(DType, DType)), All(q, Map(DType, A)),
        Hyp(Call("Function.Surjective", T)), Hyp(Call("Continuous", q)),
        Hyp(Call("Equicontinuous", Seq(n, Colon, Sp, Nat, Sp, Mapsto, Sp,
            Call("Function.iterate", T, n)))),
        Seq(Exists, Sp, M, Colon, Sp, Nat, Comma, Sp, D(0), Sp, Lt, Sp, M,
            Sp, Land, Sp, All(x, DType), Sp,
            Apply(q, Apply(Call("Function.iterate", T, M), x)), Sp, Eq, Sp, Apply(q, x))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous discrete observation of an onto compact equicontinuous system has a positive period, obtained from the finite permutation of its complete names.",
        H("Positive Periods for Discrete Observations"),
        Blocks(Describe.Lean(
            DescribeId.Create("equicontinuous-discrete-observation-positive-period"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/EquicontinuousObservationPeriod.finite_observation_period_of_equicontinuous_surjective"),
            H("From equicontinuity to a finite permutation"),
            StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
            Blocks(
                Paragraph(Text(
                    "Let D be an arbitrary compact uniform space, A a topological space with discrete "
                    + "topology, T:D→D onto, and q:D→A continuous. Assume the family of all forward "
                    + "iterates of T is equicontinuous. There is a natural number M>0 such that "
                    + "q(T^M(x))=q(x) for every x in D. The quantifier for q precedes that for M: the "
                    + "period depends on the observer. Neither A nor D is required to be finite or "
                    + "nonempty. There is no Hausdorff, zero-dimensional, metric or countability "
                    + "assumption on D, and no injectivity or invertibility assumption on T. Continuity of T follows "
                    + "from equicontinuity of the family at the iterate 1.")),
                Paragraph(Text(
                    "Define the complete name W(x)(n)=q(T^n(x)). The relation E={(x,y):q(x)=q(y)} "
                    + "is open and contains the diagonal. On a compact uniform space every such "
                    + "diagonal neighborhood is an entourage. Equicontinuity at x therefore supplies "
                    + "one neighborhood on which W(y)(n)=W(x)(n) simultaneously for all n. This proves "
                    + "local constancy of the whole-name map, a stronger assertion than continuity "
                    + "into the product topology. Compactness and IsLocallyConstant.range_finite "
                    + "make its actual image S finite; finiteness of S is a conclusion, not an input.")),
                Paragraph(Text(
                    "Left shift preserves S because W(T(x))(n)=W(x)(n+1). Onto T gives a predecessor "
                    + "for every realized name, so shift:S→S is onto and hence a finite permutation. "
                    + "Mathlib's Function.injective_iff_iterate_factorial_card_eq_id gives "
                    + "shift^(|S|!)=id. Its exponent is positive, including the empty-image case "
                    + "0!=1. The map x↦W(x), valued in S, semiconjugates T to shift. Transporting "
                    + "the factorial iterate along this semiconjugacy and evaluating coordinate zero "
                    + "gives q(T^M(x))=q(x). No global point period is asserted.")),
                Paragraph(Text(
                    "For the stable-core application, let X be a compact Hausdorff uniform space with continuous f "
                    + "and let C=⋂n range(f^n). Supply its actual compact restriction TC:C→C, its "
                    + "surjectivity, and Subtype.val∘TC=f∘Subtype.val. Equicontinuity of the ambient "
                    + "iterates on C transfers through the uniform embedding Subtype.val to "
                    + "equicontinuity of TC's iterates. Restricting each continuous finite observer q "
                    + "to C gives an observer-dependent positive period there. "
                    + "StableCoreObservation.finite_observation_range_finite_of_stable_core_periodic "
                    + "then gives finitely many complete q-names on all of X, including transient "
                    + "points. This inference assumes the stated core restriction and does not "
                    + "construct it or establish its equicontinuity.")),
                Paragraph(Text(
                    "If X is also zero-dimensional, the finite-name conclusion for every finite "
                    + "continuous observation feeds "
                    + "FiniteObservationShadowing.initial_point_tracing_of_finite_observation_names. "
                    + "For each finite open cover U, that theorem constructs a finite open control "
                    + "cover V, and every V-pseudo-orbit a is U-traced by a(0) at all natural times "
                    + "including zero. This is an application of the existing complete-name and "
                    + "control-cover results, combined with the new period construction. It supplies "
                    + "no relative Boolean extension, and Peng's general Question 5.1 remains open. "
                    + "The construction is repository-derived and makes no literature priority claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        var items = new List<Formula> { F.Id(parts[0]) };
        for (var i = 1; i < parts.Length; i++) items.AddRange([Dot, F.Id(parts[i])]);
        return Apply(Seq(Operatorname, Grp([.. items])), arguments);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
