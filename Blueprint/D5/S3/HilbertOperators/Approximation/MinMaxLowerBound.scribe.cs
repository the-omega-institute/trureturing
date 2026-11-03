using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators.Approximation;

internal sealed class MinMaxLowerBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/kitware2026minmax");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict-threshold min-max lower bounds for bounded complex Hilbert operators.",
        H("Approximation numbers and strict-threshold test subspaces"),
        Blocks(
            Describe.Lean(DescribeId.Create("errors-bdd-below"),
                DeclarationHandle.Create("D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.errors_bdd_below"),
                H("errors_bdd_below"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every error in the defining family is nonnegative, so the family is bounded below. The source and target have independent universes and complex inner-product structures; completeness is not used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("approximation-number-le-error"),
                DeclarationHandle.Create("D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number_le_error"),
                H("approximation_number_le_error"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every actual bounded rank-at-most-n map R from E to F gives approximation_number T n at most norm(T minus R). Both completeness instances are absent from this infimum bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-based-approximation-number"),
                DeclarationHandle.Create("D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number"),
                H("The zero-based approximation number"),
                StatementSource.FromAuthor(ApproximationFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a bounded complex-linear map T from E to F and a natural index n, a_n(T) is the real infimum of the operator-norm errors over bounded complex-linear R from the same E to the same F with cardinal rank at most n. Source and target have independent universes. The index is zero-based; no existence of a minimizing R is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("strict-threshold-independent-subspace"),
                DeclarationHandle.Create("D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.exists_independent_lower_bound"),
                H("Independent vectors above a strict threshold"),
                StatementSource.FromAuthor(MinMaxFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The cited published proof supplies the approximation-number definition, operator modulus, spectral cutoffs and strict-threshold min-max construction. The complex specialization uses the same continuous-functional-calculus geometry and rank-versus-error argument. The source note identifies the selected files and their attribution; the accompanying third-party license packet retains the original notices. This uses published mathematics and makes no novelty claim.")),
                    Paragraph(Text("Let E : Type u and F : Type v be complete normed additive groups with complex inner products, and let T : E →L[ℂ] F. For every n : ℕ and every r : ℝ satisfying 0 ≤ r and r < approximation_number T n, there exist s : ℝ with r < s and a : Fin (n + 1) → E. The family a is linearly independent over ℂ, and every x in the complex span of its range satisfies s * norm(x) ≤ norm(T x). There is no compactness, separability, finite-dimensionality, nontriviality, common-universe or index-below-dimension assumption.")),
                    Paragraph(Text("Set A to the positive square root of T* T and choose r < s < a_n(T). The norm identity norm(A x) = norm(T x) transports estimates for A to T. Continuous functional calculus gives the positive parts of A - s and s - A. Their product is zero, and the cocutoff is self-adjoint. Its range lies in the cutoff kernel, so it vanishes on that kernel's orthogonal complement. Positivity and the inner-product bound yield a lower modulus s on the complement and an upper modulus s on the kernel.")),
                    Paragraph(Text("If the complement has cardinal rank greater than n, it supplies n + 1 independent vectors. Otherwise its orthogonal projection P has finite rank at most n; T composed with P is an admissible bounded approximant, and the error on the complementary kernel has norm at most s. This contradicts s < a_n(T). Orthogonal projection comes from a closed Hilbert subspace; self-adjointness of a cutoff alone does not imply idempotence."))),
                DescribeRole.Theorem))));
    private static Formula Func(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);

    private static Formula Number(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula MapType() => Func("ContinuousLinearMap", Number("C"), F.Id("E"), F.Id("F"));
    private static Formula Norm(Formula value) => Func("norm", value);

    private static Formula Telescope(Formula body) =>
        All("u", Func("UniverseLevel"), All("v", Func("UniverseLevel"),
        All("E", Seq(Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("u"))),
        All("F", Seq(Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("v"))), Seq(
            OpenBracket, Func("NormedAddCommGroup", F.Id("E")), CloseBracket, Sp,
            OpenBracket, Func("InnerProductSpace", Number("C"), F.Id("E")), CloseBracket, Sp,
            OpenBracket, Func("CompleteSpace", F.Id("E")), CloseBracket, Sp,
            OpenBracket, Func("NormedAddCommGroup", F.Id("F")), CloseBracket, Sp,
            OpenBracket, Func("InnerProductSpace", Number("C"), F.Id("F")), CloseBracket, Sp,
            OpenBracket, Func("CompleteSpace", F.Id("F")), CloseBracket, Comma, Sp,
            All("T", MapType(), All("n", Number("N"), body)))))));

    private static Formula ApproximationTelescope(Formula body) =>
        All("u", Func("UniverseLevel"), All("v", Func("UniverseLevel"),
        All("E", Seq(Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("u"))),
        All("F", Seq(Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("v"))), Seq(
            OpenBracket, Func("NormedAddCommGroup", F.Id("E")), CloseBracket, Sp,
            OpenBracket, Func("InnerProductSpace", Number("C"), F.Id("E")), CloseBracket, Sp,
            OpenBracket, Func("NormedAddCommGroup", F.Id("F")), CloseBracket, Sp,
            OpenBracket, Func("InnerProductSpace", Number("C"), F.Id("F")), CloseBracket, Comma, Sp,
            All("T", MapType(), All("n", Number("N"), body)))))));

    private static Formula ApproximationFormula() => Disp(ApproximationTelescope(Seq(
        Func("approximationNumber", F.Id("T"), F.Id("n")), Sp, Eq, Sp,
        Operatorname, Grp(F.Id("inf")), Underscore, Grp(
            Typed("R", MapType()), Comma, Sp,
            Func("rank", F.Id("R")), Sp, Leq, Sp, Func("natCastCardinal", F.Id("n"))), Sp,
        Norm(Seq(F.Id("T"), Minus, F.Id("R"))))));

    private static Formula MinMaxFormula() => Disp(Telescope(All("r", Number("R"), Seq(
        D(0), Sp, Leq, Sp, F.Id("r"), Sp, Land, Sp,
        F.Id("r"), Sp, Lt, Sp, Func("approximationNumber", F.Id("T"), F.Id("n")),
        Sp, Rightarrow, Sp,
        Exists, Sp, Typed("s", Number("R")), Comma, Sp,
        F.Id("r"), Sp, Lt, Sp, F.Id("s"), Sp, Land, Sp,
        Exists, Sp, Typed("a", Seq(Func("Fin", Seq(F.Id("n"), Plus, D(1))), Sp, To, Sp, F.Id("E"))),
        Comma, Sp, Func("LinearIndependent", Number("C"), F.Id("a")), Sp, Land, Sp,
        All("x", F.Id("E"), Seq(
            F.Id("x"), Sp, InMacro, Sp, Func("span", Number("C"), Func("range", F.Id("a"))),
            Sp, Rightarrow, Sp, F.Id("s"), Sp, Norm(F.Id("x")), Sp, Leq, Sp,
            Norm(Func("T", F.Id("x")))))))));
}
