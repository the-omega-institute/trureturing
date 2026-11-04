using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ProObjects;

internal sealed class CompactObservationFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact observation fibers determine every continuous finite readout and every finite action window.",
        H("Compact Observation Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-observation-factorization"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.compact_observation_factorization"),
            H("Finite readouts and bounded action windows"),
            StatementSource.FromAuthor(Disp(Seq(
                Begin, Grp(F.Id("gathered")),
                Forall, Sp, F.Id("f"), Sp, InMacro, Sp, Call("C", F.Id("X"), F.Id("Y")),
                Comma, Sp, Exists, Sp, F.Id("N"), Comma, Sp, Exists, Bang, Sp,
                F.Id("g"), Colon, Sp, Sub(F.Id("Q"), F.Id("N")), To, Sp, F.Id("Y"),
                Comma, Sp, Forall, Sp, F.Id("x"), Comma, Sp,
                Apply(F.Id("g"), Apply(Sub(F.Id("q"), F.Id("N")), F.Id("x"))),
                Eq, Apply(F.Id("f"), F.Id("x")), Comma, RowBreak,
                Forall, Sp, F.Id("H"), Comma, Sp, Exists, Sp, F.Id("N"),
                Comma, Sp, Forall, Sp, F.Id("x"), Comma, F.Id("y"), Comma, Sp,
                Apply(Sub(F.Id("q"), F.Id("N")), F.Id("x")), Eq,
                Apply(Sub(F.Id("q"), F.Id("N")), F.Id("y")), Sp, Rightarrow, Sp,
                Forall, Sp, F.Id("w"), Comma, Sp,
                Call("length", F.Id("w")), Leq, Sp, F.Id("H"), Sp, Rightarrow, Sp,
                Apply(F.Id("o"), Apply(Sub(F.Id("F"), F.Id("w")), F.Id("x"))), Eq,
                Apply(F.Id("o"), Apply(Sub(F.Id("F"), F.Id("w")), F.Id("y"))), Dot,
                End, Grp(F.Id("gathered"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X be a nonempty compact topological space. For each natural number n, let Q_n be a finite discrete space and q_n : X → Q_n a continuous surjection. Let p_n : Q_(n+1) → Q_n satisfy q_n(x) = p_n(q_(n+1)(x)) for every x. Assume that all actual singleton fibers of all q_n form a topological basis for X. Let Y be any finite discrete space. C(X,Y) denotes all continuous maps X → Y.")),
                Paragraph(Text(
                    "The second conclusion holds for every finite action type Σ, every family of continuous total maps F_a : X → X, every continuous observation o : X → Y, and every natural horizon H. Words are all lists over Σ of length at most H. The existing runWord executes the head action first and then the tail, so F_(uv) = F_v ∘ F_u. Empty words, H = 0, empty action types, repeated actions, and noninvertible actions remain included.")),
                Paragraph(Text(
                    "Adjacent compatibility propagates equality from level N to every level n ≤ N. For each x, continuity makes the inverse image of the singleton {f(x)} open. The basis supplies a singleton observation fiber containing x inside that inverse image. IsTopologicalBasis.exists_subset_of_mem_open supplies this neighborhood directly.")),
                Paragraph(Text(
                    "IsCompact.elim_finite_subcover selects finitely many of those open fibers covering X. Take the finite supremum of their levels. Two points with equal observations at that level agree at the level of any selected fiber containing the first point; consequently both lie in that fiber and have equal f-values. This uniform fiber constancy is the compactness step.")),
                Paragraph(Text(
                    "Apply split_surjection_factorization to q_N and f, using Function.surjInv and Function.rightInverse_surjInv for the section of the actual surjection. This gives existence and uniqueness of g on the entire Q_N. The level N need not be unique. No independent inhabitant of Y is required by this construction; whenever f is given, a point of the nonempty X also supplies an element of Y.")),
                Paragraph(Text(
                    "For the window conclusion, List.finite_length_le proves that the subtype W_H of all bounded words is finite. The response map x ↦ (w ↦ o(runWord F w x)) takes values in the finite discrete product W_H → Y. Word induction and continuous_pi prove its continuity. Applying the finite-readout factorization to this response map supplies one level for the entire window. Every bounded list enters the product as its own subtype element.")),
                Paragraph(Text(
                    "Give X its Borel measurable structure and each finite discrete stage and output its discrete Borel structure. "
                    + "For fixed F, o and H, write R_H(x)(w)=o(runWord F w x) for the entire response table, indexed by all words of length at most H. "
                    + "The window conjunct makes R_H constant on each q_N fiber. Surjectivity of q_N selects a section, giving R_H=g composed with q_N on the whole finite table. "
                    + "Both maps are measurable, so for every actual source law mu its table law is exactly (mu.map q_N).map g. "
                    + "The level and factor were chosen before mu: the same pair works for every law at this fixed horizon. "
                    + "Equality of two stage laws therefore gives equality of their joint table laws. "
                    + "MeasurablePostprocessingDefectContraction.measurable_total_variation_map_le gives contraction of event TV; "
                    + "on finite stage probability laws, NativeDeclaredProbabilityPolytope.massVector_map and "
                    + "TotalVariation.DataProcessing.total_variation_channel_le give the corresponding contraction of Pinsker's half-L1 TV. "
                    + "The deterministic channel has entry one exactly at t=g(z) and zero elsewhere.")),
                Paragraph(Text(
                    "The joint table carries correlations. For example take X=Bool × Bool, observe the first coordinate, "
                    + "and let the two actions replace both coordinates by the first or by the second coordinate respectively. "
                    + "The law assigning mass one half to each of (false,false) and (true,true), and the law assigning mass one half "
                    + "to each of (false,true) and (true,false), have identical individual response laws for every word of length at most one, "
                    + "including the empty word. Their full response tables have statistical TV one: equality of the two one-action "
                    + "outputs is an event of probability one for the first law and zero for the second. "
                    + "No independence assumption or inference from separate marginals is part of the factorization.")),
                Paragraph(Text(
                    "There is also a nested-stage application of FiniteObservationVariation.exists_uniform_finite_readout_variation. "
                    + "In addition to the full telescope here, require X to be Hausdorff and zero dimensional, the stage sensors to be jointly point separating, "
                    + "both Jordan parts of each signed law s(a) to be regular, and the range of signedFunctional(s(a)) to be compact in operator norm. "
                    + "For a positive epsilon, that theorem supplies an actual finiteObservationReadout r_J retaining every variation mass within epsilon. "
                    + "Use the first conjunct here with precisely that finite discrete output to factor r_J through some q_N. "
                    + "Variation contraction for its factor gives V(s(a).map r_J) ≤ V(s(a).map q_N) ≤ V(s(a)), "
                    + "so this actual nested stage retains the same strict lower bound V(s(a))-epsilon. "
                    + "For actual probability differences the output singleton coordinates are the differences of the two pushed-forward singleton laws, "
                    + "and their statistical half-variation loses less than epsilon/2. Norm compactness is not weak-star compactness. "
                    + "The native-thread theorem InverseLimitEventTotalVariation.total_variation_eq_iSup_level has its own finite-thread carrier and measurable telescope; "
                    + "it is not an identification of arbitrary X with that thread space. Neither application gives an infinite-horizon stage "
                    + "or a common stage uniform over all horizons, laws and accuracies.")),
                Paragraph(Text(
                    "Only compactness and the actual fiber basis are used on X. The statement assumes neither a separation axiom nor a metric nor finiteness of X, and it assumes no inverse-limit representation. The conclusions are existence statements and provide no effective finite-subcover procedure or computable bound on N. OrdinaryReadout in FiniteStageReadout is a colimit of stage maps; its representative theorem alone does not establish the factorization of an arbitrary continuous map considered here."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Rewriting/Quotients/SplitSurjectionFactorization")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality"))]));

    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Apply(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
