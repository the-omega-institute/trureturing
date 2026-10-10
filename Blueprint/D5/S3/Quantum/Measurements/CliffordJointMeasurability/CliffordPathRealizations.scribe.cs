using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class CliffordPathRealizationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/mcnulty2025pathrobustness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One qubit ancilla gives a seed that anticommutes with the first path generator and commutes with all subsequent generators.",
        H("Clifford Path Realizations"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("realization", "Realization", F0(),
                "McNulty, Definition 1, p. 3: \"The anti-commutativity graph G = (V,E) of a set of observables 𝒜 is defined by {v,v′} ∈ E ⇔ A_v A_v′ = −A_v′ A_v, so that adjacent vertices correspond to anti-commuting observables, and non-adjacent vertices correspond to commuting ones.\" The carrier is Matrix (Fin d) (Fin d) ℂ with 1 ≤ d. Every observable is Hermitian and squares to the identity. Vertices are zero-indexed; the graph is Mathlib's pathGraph or cycleGraph.", "Realization",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("noisyobservable", "noisyObservable", F1(),
                "McNulty, Eq. (9), p. 3: \"A_v^η = η A_v + (tr[A_v]/d)(1−η) 𝟙\". The matrix expression retains the trace term. The definition uses TomiyamaDiagonalKPositivity.phi d (1−η) 0 at A v; expanding its scalar coefficients gives this expression.", "noisyObservable",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("effect", "effect", F2(),
                "McNulty, Eq. (3), p. 2: \"M_v(±) = ½(𝟙 ± A_v).\" The noisy binary effect replaces A_v by noisyObservable A η v. Bool true denotes +1 and false denotes −1.", "effect",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jm", "JM", F3(),
                "McNulty, Section II.C, p. 3: \"A collection of measurements are jointly measurable if there exists a parent POVM such that each measurement can be recovered as one of its marginals, or equivalently, if their statistics can be obtained from the parent after classical post-processing [47, 48].\" E is indexed by every Boolean assignment. Each E a is positive semidefinite, the total is the identity, and both sign marginals equal the noisy effects exactly.", "JM",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("visibility", "visibility", F4(),
                "The candidate threshold is (2/(2n+2)) csc(π/(2n+2)); every division in this formula is real division. It is shared by the two consecutive path sizes and the next even cycle.", "visibility",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("signed-product", "signed product", F5(),
                "This signed product identity is used in the CliffordPathRealizations construction.", "signed_product",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("generatorsign", "generatorSign", F6(),
                "The displayed expression defines generatorSign.", "generatorSign",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("prefixsign", "prefixSign", F7(),
                "The displayed expression defines prefixSign.", "prefixSign",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("prefixsign-zero", "prefixSign zero", F8(),
                "This prefixSign zero identity is used in the CliffordPathRealizations construction.", "prefixSign_zero",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("pathmajorana", "pathMajorana", F9(),
                "The displayed expression defines pathMajorana.", "pathMajorana",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("anticommuting-trace-zero", "anticommuting trace zero", F10(),
                "This anticommuting trace zero identity is used in the CliffordPathRealizations construction.", "anticommuting_trace_zero",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("noisy-eq-of-trace-zero", "noisy eq of trace zero", F11(),
                "This noisy eq of trace zero identity is used in the CliffordPathRealizations construction.", "noisy_eq_of_trace_zero",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("outcomesign", "outcomeSign", F12(),
                "The displayed expression defines outcomeSign.", "outcomeSign",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("parent-signed-marginal", "parent signed marginal", F13(),
                "This parent signed marginal identity is used in the CliffordPathRealizations construction.", "parent_signed_marginal",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("weightedhamiltonian", "weightedHamiltonian", F14(),
                "The displayed expression defines weightedHamiltonian.", "weightedHamiltonian",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("weighted-trace-bound", "weighted trace bound", F15(),
                "This weighted trace bound identity is used in the CliffordPathRealizations construction.", "weighted_trace_bound",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("path-realization-trace-zero", "path realization trace zero", F16(),
                "This path realization trace zero identity is used in the CliffordPathRealizations construction.", "path_realization_trace_zero",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("cycle-realization-trace-zero", "cycle realization trace zero", F17(),
                "This cycle realization trace zero identity is used in the CliffordPathRealizations construction.", "cycle_realization_trace_zero",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("liftpath", "liftPath", F18(),
                "The displayed expression defines liftPath.", "liftPath",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("liftseed", "liftSeed", F19(),
                "The displayed expression defines liftSeed.", "liftSeed",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("liftseed-square", "liftSeed square", F20(),
                "This liftSeed square identity is used in the CliffordPathRealizations construction.", "liftSeed_square",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("liftseed-relation", "liftSeed relation", F21(),
                "This liftSeed relation identity is used in the CliffordPathRealizations construction.", "liftSeed_relation",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("arbitrary-path-majorana-extension", "arbitrary path majorana extension", F22(),
                "One qubit ancilla gives a seed that anticommutes with the first path generator and commutes with all subsequent generators. The recursive Majorana family is Hermitian, squares to the identity, anticommutes pairwise, and has the exact consecutive bonds shown.", "arbitrary_path_majorana_extension",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("totalpath", "totalPath", F23(),
                "The displayed expression defines totalPath.", "totalPath",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("realization-majoranas", "realization majoranas", F24(),
                "This realization majoranas identity is used in the CliffordPathRealizations construction.", "realization_majoranas",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("labeled-parent-suffices", "labeled parent suffices", F25(),
                "This labeled parent suffices identity is used in the CliffordPathRealizations construction.", "labeled_parent_suffices",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("qubitv", "qubitV", F26(),
                "The displayed expression defines qubitV.", "qubitV",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("qubitv-isometry", "qubitV isometry", F27(),
                "This qubitV isometry identity is used in the CliffordPathRealizations construction.", "qubitV_isometry",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("qubitv-compress", "qubitV compress", F28(),
                "This qubitV compress identity is used in the CliffordPathRealizations construction.", "qubitV_compress",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("compressed-parent", "compressed parent", F29(),
                "This compressed parent identity is used in the CliffordPathRealizations construction.", "compressed_parent",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("paddedmajoranas", "paddedMajoranas", F30(),
                "The displayed expression defines paddedMajoranas.", "paddedMajoranas",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("paddedmajoranas-relations", "paddedMajoranas relations", F31(),
                "This paddedMajoranas relations identity is used in the CliffordPathRealizations construction.", "paddedMajoranas_relations",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("paddedmajoranas-bond", "paddedMajoranas bond", F32(),
                "This paddedMajoranas bond identity is used in the CliffordPathRealizations construction.", "paddedMajoranas_bond",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("quadratic", "Quadratic", F33(),
                "The displayed expression defines Quadratic.", "Quadratic",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("quadratic-bound-of-positive-split", "quadratic bound of positive split", F34(),
                "This quadratic bound of positive split identity is used in the CliffordPathRealizations construction.", "quadratic_bound_of_positive_split",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("sum-fin-next", "sum fin next", F35(),
                "This sum fin next identity is used in the CliffordPathRealizations construction.", "sum_fin_next",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("sum-fin-prev", "sum fin prev", SumFinPrev(),
                "The previous-index sum selects the preceding coordinate when it exists, and is zero at the left endpoint.", "sum_fin_prev",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("tridiagonal", "tridiagonal", F36(),
                "The displayed expression defines tridiagonal.", "tridiagonal",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("tridiagonal-mul-apply", "tridiagonal mul apply", F37(),
                "This tridiagonal mul apply identity is used in the CliffordPathRealizations construction.", "tridiagonal_mul_apply",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("mul-tridiagonal-apply", "mul tridiagonal apply", F38(),
                "This mul tridiagonal apply identity is used in the CliffordPathRealizations construction.", "mul_tridiagonal_apply",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("edgevector", "edgeVector", F39(),
                "The displayed expression defines edgeVector.", "edgeVector",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("weightedlap", "weightedLap", F40(),
                "The displayed expression defines weightedLap.", "weightedLap",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("weightedlap-psd", "weightedLap psd", F41(),
                "This weightedLap psd identity is used in the CliffordPathRealizations construction.", "weightedLap_psd",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("weightedlap-apply", "weightedLap apply", F42(),
                "This weightedLap apply identity is used in the CliffordPathRealizations construction.", "weightedLap_apply",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Call(owner), Dot, Call(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula F0() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Call("SimpleGraph"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Call("Realization"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Eq, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Iff, Sp, Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("d"), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("IsHermitian"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Sp, Comma, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Sp, Comma, Sp, F.Id("u"), Sp, Neq, Sp, F.Id("v"), Sp, To, Sp, F.Id("G"), Sp, Dot, Sp, Call("Adj"), Sp, F.Id("u"), Sp, F.Id("v"), Sp, To, Sp, F.Id("A"), Sp, F.Id("u"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("u"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Sp, Comma, Sp, F.Id("u"), Sp, Neq, Sp, F.Id("v"), Sp, To, Sp, Neg, Sp, F.Id("G"), Sp, Dot, Sp, Call("Adj"), Sp, F.Id("u"), Sp, F.Id("v"), Sp, To, Sp, F.Id("A"), Sp, F.Id("u"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Eq, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("u"))))))
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Parenthesized(Seq(Call("noisyObservable"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Eq, Sp, F.Id("eta"))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Eq, Sp, F.Id("v"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Plus, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Slash, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Cdot, Sp, D(1))))
        ]));

    private static Formula F2() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Call("Bool"))), Comma),
            Seq(Parenthesized(Seq(Call("effect"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Eq, Sp, F.Id("eta"))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Eq, Sp, F.Id("v"))), Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Eq, Sp, F.Id("s"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("s"), Sp, Call("then"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, Call("noisyObservable"), Sp, F.Id("A"), Sp, F.Id("eta"), Sp, F.Id("v"))))))
        ]));

    private static Formula F3() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Call("JM"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("eta"), Sp, Colon, Sp, Eq, Sp, F.Id("eta"))), Sp, Iff, Sp, Parenthesized(Seq(Exists, Sp, Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Sp, To, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("E"), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))), Sp, Land, Sp, Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Call("Bool"))), Sp, Comma, Sp, Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, InMacro, Sp, Call("Finset"), Sp, Dot, Sp, Call("univ"), Sp, Dot, Sp, Call("filter"), Sp, Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Sp, Mapsto, Sp, F.Id("a"), Sp, F.Id("v"), Sp, Eq, Sp, F.Id("s"))), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"))), Sp, Eq, Sp, Call("effect"), Sp, F.Id("A"), Sp, F.Id("eta"), Sp, F.Id("v"), Sp, F.Id("s"))))))
        ]));

    private static Formula F4() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("visibility"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Eq, Sp, F.Id("n"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(2), Sp, Slash, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(2))))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("pi"), Sp, Slash, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(2)))))))), Seq(Minus, D(1))))))
        ]));

    private static Formula F5() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("x"), Sp, Eq, Sp, F.Id("s"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("x"), Sp, Cdot, Sp, F.Id("a"))))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp, F.Id("x"), Sp, Eq, Sp, F.Id("t"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("x"), Sp, Cdot, Sp, F.Id("b"))))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Cdot, Sp, F.Id("x"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("s"), Sp, Cdot, Sp, F.Id("t"))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("x"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))))))
        ]));

    private static Formula F6() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("generatorSign"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("k"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("j"), Sp, Lor, Sp, F.Id("j"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Call("then"), Sp, Minus, Sp, D(1), Sp, Call("else"), Sp, D(1))))
        ]));

    private static Formula F7() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("prefixSign"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("j"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Lor, Sp, F.Id("j"), Sp, Eq, Sp, F.Id("k"), Sp, Call("then"), Sp, Minus, Sp, D(1), Sp, Call("else"), Sp, D(1))))
        ]));

    private static Formula F8() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("prefixSign"), Sp, D(0), Sp, F.Id("j"), Sp, Eq, Sp, Call("if"), Sp, F.Id("j"), Sp, Eq, Sp, D(0), Sp, Call("then"), Sp, Minus, Sp, D(1), Sp, Call("else"), Sp, D(1))
        ]));

    private static Formula F9() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Call("pathMajorana"), Sp, F.Id("A"), Sp, F.Id("q"), Sp, D(0), Sp, Eq, Sp, F.Id("q"))), Sp, Land, Sp, Parenthesized(Seq(Call("pathMajorana"), Sp, F.Id("A"), Sp, F.Id("q"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, Minus, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(Call("pathMajorana"), Sp, F.Id("A"), Sp, F.Id("q"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("k"))))))
        ]));

    private static Formula F10() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("B"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("B"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("A"))))), Sp, To),
            Seq(F.Id("A"), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))
        ]));

    private static Formula F11() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Call("noisyObservable"), Sp, F.Id("A"), Sp, F.Id("t"), Sp, F.Id("v"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"))
        ]));

    private static Formula F12() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Call("Bool"))), Comma),
            Seq(Parenthesized(Seq(Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Eq, Sp, F.Id("b"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("b"), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, Minus, Sp, D(1))))
        ]));

    private static Formula F13() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, F.Id("s"), Sp, Comma, Sp, Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, InMacro, Sp, Call("Finset"), Sp, Dot, Sp, Call("univ"), Sp, Dot, Sp, Call("filter"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("a"), Sp, Mapsto, Sp, F.Id("a"), Sp, F.Id("v"), Sp, Eq, Sp, F.Id("s"))), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"))), Sp, Eq, Sp, Call("effect"), Sp, F.Id("A"), Sp, F.Id("t"), Sp, F.Id("v"), Sp, F.Id("s"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, Comma, Sp, Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("E"), Sp, F.Id("a"))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"))
        ]));

    private static Formula F14() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Comma),
            Seq(Parenthesized(Seq(Call("weightedHamiltonian"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Eq, Sp, F.Id("w"))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Eq, Sp, F.Id("a"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("v"))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("w"), Sp, F.Id("v"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"))))
        ]));

    private static Formula F15() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("d"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Call("JM"), Sp, F.Id("A"), Sp, F.Id("t"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("a"), Sp, Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Minus, Sp, Call("weightedHamiltonian"), Sp, F.Id("A"), Sp, F.Id("w"), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))), Sp, To),
            Seq(F.Id("t"), Sp, Cdot, Sp, Parenthesized(Seq(Sum, Sp, F.Id("v"), Sp, Comma, Sp, F.Id("w"), Sp, F.Id("v"))), Sp, Leq, Sp, F.Id("c"))
        ]));

    private static Formula F16() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("m"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("pathGraph"), Sp, F.Id("m"))), Sp, F.Id("A"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))
        ]));

    private static Formula F17() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("m"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("cycleGraph"), Sp, F.Id("m"))), Sp, F.Id("A"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))
        ]));

    private static Formula F18() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("liftPath"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("k"), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("k"), Sp, Eq, Sp, D(0), Sp, Call("then"), Sp, Call("qubitZ"), Sp, Call("else"), Sp, D(1))))))
        ]));

    private static Formula F19() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("liftSeed"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Call("qubitX"))))
        ]));

    private static Formula F20() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("liftSeed"), Sp, F.Id("d"), Sp, Cdot, Sp, Call("liftSeed"), Sp, F.Id("d"), Sp, Eq, Sp, D(1))
        ]));

    private static Formula F21() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("liftSeed"), Sp, F.Id("d"), Sp, Cdot, Sp, Call("liftPath"), Sp, F.Id("A"), Sp, F.Id("j"), Sp, Eq, Sp, Call("prefixSign"), Sp, D(0), Sp, F.Id("j"), Sp, Cdot, Sp, Parenthesized(Seq(Call("liftPath"), Sp, F.Id("A"), Sp, F.Id("j"), Sp, Cdot, Sp, Call("liftSeed"), Sp, F.Id("d"))))
        ]));

    private static Formula F22() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, F.Id("A"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("k"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("k"))), Sp, Dot, Sp, Call("IsHermitian"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, F.Id("j"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, F.Id("j"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, F.Id("A"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("j"), Sp, Eq, Sp, Call("generatorSign"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("k"))))), Sp, To),
            Seq(Call("let"), Sp, F.Id("g"), Sp, Colon, Sp, Eq, Sp, Call("pathMajorana"), Sp, Parenthesized(Seq(Call("liftPath"), Sp, F.Id("A"))), Sp, Parenthesized(Seq(Call("liftSeed"), Sp, F.Id("d"))), Sp, Semi, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("k"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("j"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("i"), Sp, Lt, Sp, F.Id("j"), Sp, To, Sp, F.Id("g"), Sp, F.Id("i"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("i"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Eq, Sp, Call("liftPath"), Sp, F.Id("A"), Sp, F.Id("k"))))
        ]));

    private static Formula F23() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("totalPath"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, Call("hk"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, Call("then"), Sp, F.Id("A"), Sp, Seq(Langle, Sp, Seq(F.Id("k"), Sp, Comma, Sp, Call("hk")), Sp, Rangle), Sp, Call("else"), Sp, D(1))))
        ]));

    private static Formula F24() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("pathGraph"), Sp, F.Id("m"))), Sp, F.Id("A"))), Sp, To),
            Seq(Call("let"), Sp, F.Id("g"), Sp, Colon, Sp, Eq, Sp, Call("pathMajorana"), Sp, Parenthesized(Seq(Call("liftPath"), Sp, Parenthesized(Seq(Call("totalPath"), Sp, F.Id("A"))))), Sp, Parenthesized(Seq(Call("liftSeed"), Sp, F.Id("d"))), Sp, Semi, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("k"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("j"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("i"), Sp, Lt, Sp, F.Id("j"), Sp, To, Sp, F.Id("g"), Sp, F.Id("i"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("i"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("m"), Sp, To, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Eq, Sp, Call("liftPath"), Sp, Parenthesized(Seq(Call("totalPath"), Sp, F.Id("A"))), Sp, F.Id("k"))))
        ]));

    private static Formula F25() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("Omega"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, F.Id("Omega")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(Call("label"), Sp, Colon, Sp, F.Id("Omega"), Sp, To, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("P"), Sp, Colon, Sp, F.Id("Omega"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, Omega, Sp, Comma, Sp, Parenthesized(Seq(F.Id("P"), Sp, Omega)), Sp, Dot, Sp, Call("PosSemidef"))), Sp, To),
            Seq(Parenthesized(Seq(Sum, Sp, Omega, Sp, Comma, Sp, F.Id("P"), Sp, Omega, Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Sum, Sp, Omega, Sp, Comma, Sp, Call("outcomeSign"), Sp, Parenthesized(Seq(Call("label"), Sp, Omega, Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("P"), Sp, Omega, Sp, Eq, Sp, Call("noisyObservable"), Sp, F.Id("A"), Sp, F.Id("t"), Sp, F.Id("v"))), Sp, To),
            Seq(Call("JM"), Sp, F.Id("A"), Sp, F.Id("t"))
        ]));

    private static Formula F26() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Iota, Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Iota, Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Iota, Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Dot, Sp, Call("submatrix"), Sp, Call("id"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("v"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("v"), Sp, Comma, Sp, D(0))))))))
        ]));

    private static Formula F27() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)))), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)))), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))))
        ]));

    private static Formula F28() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("D"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)))), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("A"), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, F.Id("D"))), Sp, Cdot, Sp, Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)))), Sp, Eq, Sp, F.Id("D"), Sp, D(0), Sp, D(0), Sp, Cdot, Sp, F.Id("A"))
        ]));

    private static Formula F29() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(F.Id("V"), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, F.Id("V"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, F.Id("V"), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, F.Id("B"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("V"), Sp, Eq, Sp, F.Id("A"), Sp, F.Id("v"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Call("Bool"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("a"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("E"), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))), Sp, To),
            Seq(Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Sum, Sp, F.Id("a"), Sp, Comma, Sp, Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("B"), Sp, F.Id("v"))), Sp, To),
            Seq(Call("JM"), Sp, F.Id("A"), Sp, F.Id("t"))
        ]));

    private static Formula F30() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Plus, Sp, D(2))))), Comma),
            Seq(Parenthesized(Seq(Call("paddedMajoranas"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Iota, Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Iota, Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Eq, Sp, D(0), Sp, Call("then"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Call("qubitX"), Sp, Call("else"), Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Call("qubitZ"))))
        ]));

    private static Formula F31() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("k"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, F.Id("l"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, F.Id("l"), Sp, Leq, Sp, F.Id("m"), Sp, To, Sp, F.Id("k"), Sp, Neq, Sp, F.Id("l"), Sp, To, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("l"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("l"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"))))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("paddedMajoranas"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(Call("paddedMajoranas"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("j"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, Call("paddedMajoranas"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Eq, Sp, F.Id("m"))), Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("j"))))))
        ]));

    private static Formula F32() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(F.Id("m"), Sp, Plus, Sp, D(2))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(Call("hnext"), Sp, Colon, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, F.Id("m"), Sp, Plus, Sp, D(2))), Comma),
            Seq(Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(Call("paddedMajoranas"), Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, Call("paddedMajoranas"), Sp, F.Id("g"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, Call("hnext")), Sp, Rangle))), Sp, Eq, Sp, Parenthesized(Seq(Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, Parenthesized(Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"))))), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))
        ]));

    private static Formula F33() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("C"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Call("Quadratic"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Eq, Sp, F.Id("M"))), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("C"), Sp, Colon, Sp, Eq, Sp, F.Id("C"))), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, F.Id("j"), Sp, Comma, Sp, Sum, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("C"), Sp, F.Id("j"), Sp, F.Id("k"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"))))))
        ]));

    private static Formula F34() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("P"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("Q"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(F.Id("P"), Sp, Dot, Sp, Call("PosSemidef"))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("Q"), Sp, Dot, Sp, Call("PosSemidef"))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("K"), Sp, Eq, Sp, F.Id("P"), Sp, Minus, Sp, F.Id("Q"))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("P"), Sp, Dot, Sp, Call("trace"), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Minus, Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Call("Quadratic"), Sp, F.Id("g"), Sp, F.Id("K"))), Sp, Dot, Sp, Call("PosSemidef"))
        ]));

    private static Formula F35() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("AddCommMonoid"), Sp, F.Id("S")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, F.Id("S"))), Comma),
            Seq(Parenthesized(Seq(Sum, Sp, F.Id("k"), Sp, Comma, Sp, Call("if"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("f"), Sp, F.Id("k"), Sp, Call("else"), Sp, D(0))), Sp, Eq, Sp, Call("if"), Sp, F.Id("h"), Sp, Colon, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, F.Id("M"), Sp, Call("then"), Sp, F.Id("f"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, F.Id("h")), Sp, Rangle), Sp, Call("else"), Sp, D(0))
        ]));

    private static Formula SumFinPrev() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("AddCommMonoid"), Sp, F.Id("S")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, F.Id("S"))), Comma),
            Seq(Parenthesized(Seq(Sum, Sp, F.Id("k"), Sp, Comma, Sp, Call("if"), Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("f"), Sp, F.Id("k"), Sp, Call("else"), Sp, D(0))), Sp, Eq, Sp, Call("if"), Sp, F.Id("h"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("f"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Call("by"), Sp, Call("omega")), Sp, Rangle), Sp, Call("else"), Sp, D(0))
        ]));

    private static Formula F36() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Call("tridiagonal"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Eq, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Eq, Sp, F.Id("w"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Dot, Sp, Call("diagonal"), Sp, F.Id("d"), Sp, Plus, Sp, Call("Matrix"), Sp, Dot, Sp, Call("of"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("j"), Sp, F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, Mapsto, Sp, Call("if"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("w"), Sp, F.Id("j"), Sp, Call("else"), Sp, D(0))), Sp, Plus, Sp, Call("Matrix"), Sp, Dot, Sp, Call("transpose"), Sp, Parenthesized(Seq(Call("Matrix"), Sp, Dot, Sp, Call("of"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("j"), Sp, F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, Mapsto, Sp, Call("if"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("w"), Sp, F.Id("j"), Sp, Call("else"), Sp, D(0))))))))
        ]));

    private static Formula F37() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("N"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("N"))), Comma),
            Seq(Parenthesized(Seq(Call("tridiagonal"), Sp, F.Id("M"), Sp, F.Id("d"), Sp, F.Id("w"), Sp, Cdot, Sp, F.Id("F"))), Sp, F.Id("j"), Sp, F.Id("r"), Sp, Eq, Sp, F.Id("d"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("F"), Sp, F.Id("j"), Sp, F.Id("r"), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("h"), Sp, Colon, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, F.Id("M"), Sp, Call("then"), Sp, F.Id("w"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("F"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, F.Id("h")), Sp, Rangle), Sp, F.Id("r"), Sp, Call("else"), Sp, D(0))), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, D(0), Sp, Lt, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("w"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Cdot, Sp, F.Id("F"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, F.Id("r"), Sp, Call("else"), Sp, D(0))))
        ]));

    private static Formula F38() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("N"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("N"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Parenthesized(Seq(F.Id("F"), Sp, Cdot, Sp, Call("tridiagonal"), Sp, F.Id("M"), Sp, F.Id("d"), Sp, F.Id("w"))), Sp, F.Id("j"), Sp, F.Id("r"), Sp, Eq, Sp, F.Id("F"), Sp, F.Id("j"), Sp, F.Id("r"), Sp, Cdot, Sp, F.Id("d"), Sp, F.Id("r"), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("h"), Sp, Colon, Sp, F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, F.Id("M"), Sp, Call("then"), Sp, F.Id("F"), Sp, F.Id("j"), Sp, Seq(Langle, Sp, Seq(F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, F.Id("h")), Sp, Rangle), Sp, Cdot, Sp, F.Id("w"), Sp, F.Id("r"), Sp, Call("else"), Sp, D(0))), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, D(0), Sp, Lt, Sp, F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, F.Id("F"), Sp, F.Id("j"), Sp, Seq(Langle, Sp, Seq(F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Cdot, Sp, F.Id("w"), Sp, Seq(Langle, Sp, Seq(F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Call("else"), Sp, D(0))))
        ]));

    private static Formula F39() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Parenthesized(Seq(Call("edgeVector"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Eq, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Eq, Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Pi"), Sp, Dot, Sp, Call("single"), Sp, F.Id("r"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, F.Id("j"), Sp, Minus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("r"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))))))
        ]));

    private static Formula F40() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Call("weightedLap"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Eq, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Eq, Sp, F.Id("b"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("M"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, F.Id("r"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("b"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Call("Matrix"), Sp, Dot, Sp, Call("vecMulVec"), Sp, Parenthesized(Seq(Call("edgeVector"), Sp, F.Id("M"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Call("star"), Sp, Parenthesized(Seq(Call("edgeVector"), Sp, F.Id("M"), Sp, F.Id("r"))))))))
        ]));

    private static Formula F41() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, Comma, Sp, D(0), Sp, Leq, Sp, F.Id("b"), Sp, F.Id("r"))), Sp, To),
            Seq(Parenthesized(Seq(Call("weightedLap"), Sp, F.Id("M"), Sp, F.Id("b"))), Sp, Dot, Sp, Call("PosSemidef"))
        ]));

    private static Formula F42() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Call("weightedLap"), Sp, F.Id("M"), Sp, F.Id("b"), Sp, F.Id("j"), Sp, F.Id("k"), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("j"), Sp, Eq, Sp, F.Id("k"), Sp, Call("then"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("b"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, D(0), Sp, Lt, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, Parenthesized(Seq(F.Id("b"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Minus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0))))), Sp, Call("else"), Sp, D(0))), Sp, Minus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, Parenthesized(Seq(F.Id("b"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0))), Sp, Minus, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("k"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("j"), Sp, Dot, Sp, Call("val"), Sp, Call("then"), Sp, Parenthesized(Seq(F.Id("b"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0))))
        ]));
}
