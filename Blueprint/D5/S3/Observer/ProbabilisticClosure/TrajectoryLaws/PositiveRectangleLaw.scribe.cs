using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class PositiveRectangleLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual law excludes supported positive rectangular words", H("The actual law excludes supported positive rectangular words"),
        Blocks(
            Describe.Lean(DescribeId.Create("supported-word-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.supported_word_obstruction"),
                H("General same-law supported-word exclusion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every stationary finite marked presentation, suppose every legal output cylinder is positive and the native complete-exterior posterior is the actual bit almost surely. Every positive word product has no nonempty exact positive rectangular support. The no11 condition of Presentation makes every positive word legal. Protected words w0x0w for both x are legal and positive; arbitrary nonnegative farther messages give a uniform two-sided posterior interval on the positive guard. Native finite exterior conditional expectations converge to the complete exterior on this same law, contradicting the binary full posterior. Zero-total atoms require no normalization, and the matrix support need not have rank one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-trimmed-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_trimmed_obstruction"),
                H("The complete-law positive trimming boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every stationary finite presentation θ of the actual P, positive-mass trimming has complete visible law equal to θ and every trimmed word product excludes nonempty exact positive rectangular support. The original same-law trimming cylinder identity and complete bilateral cylinder uniqueness identify the canonical trimmed law. Strict positivity of every retained initial mass makes a rectangular product a positive-probability word. The empty word, structural zeros and original zero-mass states stay within the stated scope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-irreducible-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_irreducible_obstruction"),
                H("Every irreducible same-law presentation is excluded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite stationary marked presentation of the original twelve-state visible law, assume that each ordered hidden-state pair has a strictly positive transition-power entry at some natural time. Then no original word matrix at any length has nonempty exact positive rectangular support. Stationarity and this reachability first imply strictly positive stationary mass at every state, so any such word would have positive occurrence probability and contradict actual_every_presentation. No aperiodicity or rank-one hypothesis is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("guard"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.guard"),
                H("The protected exterior event"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("guard(w) fixes the finite word w followed by zero on coordinates -(length(w)+1) through -1, and zero followed by w on coordinates one through length(w)+1. The missing center is unconstrained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-every-presentation"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_every_presentation"),
                H("Every presentation of the same output law is excluded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite hidden type with measurable singletons, every stationary marked presentation theta with visibleLaw(theta) equal to the original twelve-state visible law, every length n and every Boolean word w of strictly positive actual occurrence probability, its original word matrix cannot have nonempty exact positive rectangular support. All included entries are positive, all other entries are zero; rank is unrestricted. The proof expresses actual finite exterior atoms as original matrix products, decomposes every farther completion into nonnegative actual row and column messages, and applies one uniform epsilon to both protected center masses. Both protected words are legal and have positive actual mass. Zero-total atoms are never normalized. The native finite conditional distribution equals the actual cell ratio; the increasing exterior filtration and same-law full-erasure theorem give the contradiction on the positive guard event. Equality of the entire visible measures, rather than separate-radius identities, transports this argument to every presentation. Unsupported ghost words are outside this conclusion."))), DescribeRole.Theorem))));
}
