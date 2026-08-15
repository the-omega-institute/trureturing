using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class GreenClassWindowDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite naming-window KL divergence is additive across coordinates, identifies the " +
        "uniform entropy defect, and vanishes exactly at coordinatewise agreement.",
        H("Green-Class Window Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-divergence-is-additive"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw"),
                H("Window divergence is the sum of coordinate divergences"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("KL")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    Operatorname, Grp(F.Id("KL")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For normalized coordinate laws p_i and strictly positive p_i and q_i, " +
                        "the logarithm of the quotient of the two coordinate products splits " +
                        "into a finite sum. Interchanging the finite sums isolates one KL term " +
                        "per coordinate.")),
                    Paragraph(Text(
                        "Normalization is required only for p in this additivity theorem. Strict " +
                        "positivity keeps the product logarithm and every coordinate quotient in " +
                        "the elementary real-valued KL regime used by the proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-coordinates-give-the-uniform-window-law"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.windowLaw_uniform_eq"),
                H("Uniform coordinates give the uniform window law"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("u"), Close,
                    Sp, Eq, Sp,
                    Open, F.Id("w"), Mapsto, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("W"), Close,
                    Caret, Grp(Minus, D(1)), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here u is the coordinate law with constant mass one over card O, and W " +
                        "is the finite type of assignments from the coordinate set to O. The " +
                        "coordinate product is therefore the reciprocal of card W at every " +
                        "assignment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-window-divergence-is-the-entropy-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_uniform_eq"),
                H("Uniform window divergence is the naming entropy defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("KL")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("u"), Close, Close,
                    Sp, Eq, Sp,
                    F.Id("n"), Sp, Times, Sp,
                    Open,
                    Operatorname, Grp(F.Id("namingDim")), Open, F.Id("O"), Close,
                    Sp, Times, Sp, Log, Grp(D(2)), Close,
                    Sp, Minus, Sp,
                    F.Id("H"), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonnegative normalized coordinate family p and a nonempty alphabet " +
                        "O, the product window law is normalized. Divergence from the uniform " +
                        "assignment law is therefore its log-cardinality entropy deficit.")),
                    Paragraph(Text(
                        "The cardinality of the assignment type is card O raised to the number n " +
                        "of coordinates. Taking its logarithm and using the definition of namingDim " +
                        "gives the displayed defect in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-window-divergence-characterizes-coordinatewise-agreement"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_eq_zero_iff"),
                H("Zero window divergence characterizes coordinatewise agreement"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("KL")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("i")),
                    Sp, Eq, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonnegative normalized and strictly positive coordinate laws p and q, " +
                        "additivity expresses window divergence as a sum of nonnegative coordinate " +
                        "divergences. A zero sum forces every coordinate term to vanish, and Gibbs " +
                        "equality then gives p_i = q_i.")),
                    Paragraph(Text(
                        "Strict positivity is retained deliberately. Extending the result to " +
                        "coordinate laws with zero support requires a separate support-aware " +
                        "generalization and is outside this module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("green-class-window-divergence-is-the-coordinate-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_greenClass_window"),
                H("Green-class window divergence is the coordinate sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("KL")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("mu"), Close, Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("nu"), Close, Close, Close,
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("S")), Sp,
                    Operatorname, Grp(F.Id("KL")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("mu"), Comma, Sp, F.Id("i"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("nu"), Comma, Sp, F.Id("i"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two families of probability measures, each finite green-class window " +
                        "is the product of the singleton coordinate masses indexed by S. Under " +
                        "strict positivity, window additivity identifies its KL divergence with " +
                        "the sum of the coordinate divergences over S.")),
                    Paragraph(Text(
                        "The proof re-establishes two helpers that are private in the frozen " +
                        "GreenClassWindowEntropy module: finite sum-product factorization and " +
                        "normalization of coordinate singleton masses. Their proofs are repeated " +
                        "here because a frozen module cannot be reopened merely to export them."))),
                DescribeRole.Theorem))));
}
