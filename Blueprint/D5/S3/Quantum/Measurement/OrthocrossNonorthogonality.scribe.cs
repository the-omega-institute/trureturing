using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OrthocrossNonorthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/debrota2020varieties");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthocross Gram entries are weighted squared moduli of inverse-frame pairings. "
            + "Every entry is strictly positive, and all entries tend uniformly to zero as the "
            + "dimension increases.",
        H("Inverse-frame pairings of orthocross measurements"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orthocross-nonorthogonality-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Nonorthogonality and uniform decay"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("d"), Comma, Sp, F.Id("U"), Comma, Sp, Alpha, Comma, Sp, Beta, Comma, Sp,
                    Alpha, Sp, Neq, Sp, Beta, Sp, Rightarrow, Sp,
                    D(0), Sp, Lt, Sp, Entry(), Close, Sp, Land, Sp,
                    Open, Forall, Sp, Epsilon, Sp, Gt, Sp, D(0), Comma, Sp,
                    Exists, Sp, Sub("d", D(0)), Comma, Sp,
                    Forall, Sp, F.Id("d"), Sp, Geq, Sp, Sub("d", D(0)), Comma, Sp,
                    Forall, Sp, F.Id("U"), Comma, Sp, Alpha, Comma, Sp, Beta, Comma, Sp,
                    Norm(Entry()), Sp, Lt, Sp, Epsilon, Close))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The dimension d is any natural number, U is any unitary d by d complex matrix, "
                        + "and alpha and beta run over the basis, real cross and imaginary cross indices. "
                        + "Strict complex positivity means a strictly positive real value. The second "
                        + "clause is uniform in both the basis and the indices. The inverse-frame pairing "
                        + "identity connects strict positivity to nonvanishing of the vector pairings."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orthocross-inverse-frame-pairing"),
                DeclarationHandle.Create(Prefix + "gram_eq_norm_sq"),
                H("Weighted squared modulus"),
                StatementSource.FromAuthor(Disp(Seq(
                    Entry(), Sp, Eq, Sp, Sub("w", Alpha), Sp, Sub("w", Beta), Sp,
                    Norm(Seq(Sub("v", Alpha), Caret, Grp(Star), Sp,
                        F.Id("M"), Sp, Sub("v", Beta))), Caret, Grp(D(2)), Comma, Quad, Sp,
                    F.Id("M"), Sp, Eq, Sp, F.Omega, Caret, Grp(Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Omega is the standard-basis frame. Unitary covariance reduces each Gram entry "
                        + "to tr(Pi_alpha M Pi_beta M). Multiplication of the two rank-one projectors "
                        + "gives the product of the inverse-frame pairing and its complex conjugate, "
                        + "because M is Hermitian. The weights are 1 for basis indices and 1/2 for cross indices."))),
                DescribeRole.Theorem),
            Estimate("frame_lower_bound", "A lower bound for the frame",
                Seq(Frac(F.Id("d"), D(4)), Sp, F.Id("I"), Sp, Leq, Sp, F.Omega),
                "The standard-basis frame has d on the diagonal and (1 - i)/2 or (1 + i)/2 "
                    + "away from the diagonal. Every off-diagonal modulus is at most 3/4. "
                    + "Gershgorin's theorem applied after subtracting (d/4)I shows that "
                    + "every eigenvalue of the difference is nonnegative."),
            Estimate("inverse_frame_norm_bound", "An operator norm bound for the inverse",
                Seq(F.Id("d"), Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Norm(Seq(F.Omega, Caret, Grp(Minus, D(1)))), Sp, Leq, Sp,
                    Frac(D(4), F.Id("d"))),
                "In positive dimension, inverse order reverses the frame lower bound. "
                    + "The inverse is positive semidefinite, so its operator norm is at most 4/d."),
            Estimate("gram_norm_bound", "A bound for every Gram entry",
                Seq(F.Id("d"), Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Norm(Entry()), Sp, Leq, Sp, Frac(D(2, 5, 6), Seq(F.Id("d"), Caret, Grp(D(2))))),
                "Each unnormalised orthocross vector has Euclidean norm at most two. "
                    + "Cauchy-Schwarz and the inverse norm bound give pairing modulus at most 16/d. "
                    + "The weights are at most one, and the squared-modulus identity therefore "
                    + "bounds every Gram entry by 256 divided by d squared, uniformly in the basis and indices."),
            Estimate("gram_uniform_decay", "Uniform decay with dimension",
                Seq(Forall, Sp, Epsilon, Sp, Gt, Sp, D(0), Comma, Sp,
                    Exists, Sp, Sub("d", D(0)), Comma, Sp,
                    Forall, Sp, F.Id("d"), Sp, Geq, Sp, Sub("d", D(0)), Comma, Sp,
                    Forall, Sp, F.Id("U"), Comma, Sp, Alpha, Comma, Sp, Beta, Comma, Sp,
                    Norm(Entry()), Sp, Lt, Sp, Epsilon),
                "Choose a natural number larger than both 1 and 256/epsilon. For every "
                    + "dimension at least that number, the uniform Gram bound is strictly "
                    + "less than epsilon. This establishes the second clause of the assertion."),
            Estimate("gram_pos", "Strict positivity of every Gram entry",
                Seq(Forall, Sp, F.Id("U"), Comma, Sp, Alpha, Comma, Sp, Beta, Comma, Sp,
                    D(0), Sp, Lt, Sp, Entry()),
                "Every inverse-frame pairing is nonzero. Its squared modulus is strictly positive, "
                    + "and both orthocross weights are positive. The weighted squared-modulus identity "
                    + "therefore gives strict complex positivity, which means that the entry is a "
                    + "strictly positive real number. This includes equal indices."),
            Estimate("result", "Positivity and uniform decay",
                Seq(F.Id("claim")),
                "Strict positivity of every entry implies the first clause for distinct indices. "
                    + "The uniform decay bound supplies the second clause. Both hold for every "
                    + "dimension and every unitary basis; dimension zero has an empty index set. "
                    + "The proof uses the closed geometric inverse and the Gaussian rational-root "
                    + "obstruction for its pairing polynomials.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debrota-2020-orthocross-nonorthogonality"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Estimate(
        string declaration, string title, Formula formula, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("orthocross-" + declaration.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula Entry() => Seq(Sub("G", Seq(Alpha, Beta)), Open, F.Id("U"), Close);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Epsilon => Varepsilon;
    private static Formula Frac(Formula numerator, Formula denominator) =>
        Seq(F.Frac, Grp(numerator), Grp(denominator));
}
