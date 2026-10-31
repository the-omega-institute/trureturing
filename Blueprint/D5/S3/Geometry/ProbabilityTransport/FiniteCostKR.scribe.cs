using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class FiniteCostKRDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Geometry/miller2026vlasovot");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "General cost probability transport",
        H("General cost probability transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finitecostkr-finite-kr-attained"),
                DeclarationHandle.Create("D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.finite_kr_attained"),
                H("Finite equality and attained maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let I be any finite type, a and b nonnegative real weights of total mass one, and c a nonnegative symmetric triangular self-zero cost. There exist an actual nonnegative matrix P with exactly these row and column sums and a real potential f with absolute oscillation bounded by c. The matrix cost equals the signed weighted potential difference; it is no larger than the cost of any other feasible matrix, and the potential difference is no smaller than that of any other admissible potential. Zero coordinates are allowed, and the empty-type contradiction follows from mass one. The frozen finite strong-duality theorem supplies unrestricted u and v and the actual optimal matrix; the finite c-transform is the maximum of u(a)-c(x,a), rather than an unsupported substitution v=-u. Finite marginal identities prove the weak comparison and force equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitecostkr-wassersteincostcoupling-le-dual"),
                DeclarationHandle.Create("D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.wassersteinCostCoupling_le_dual"),
                H("General cost Kantorovich Rubinstein inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every second-countable Borel standard-Borel pseudometric space, every continuous nonnegative self-zero symmetric triangular cost c bounded above by distance, any probability measures mu and nu, and any explicit basepoint x0 with integrable c(.,x0) for both measures, the ENNReal infimum over all actual coupling measures of the lower integral of ofReal(c) is at most the supremum over all real functions f with absolute oscillation bounded by c of ofReal(integral f mu minus integral f nu). Both finite-range pushforwards are decomposed into their actual atom masses on the union of their finite ranges. The attained finite KR theorem supplies its matrix and single potential on this common support. A finite c-transform extends the potential without changing its values there; the weighted Dirac law has exact marginals and lower-integral cost exactly equal to the signed integral objective. Cost approximation, actual coupling gluing, and dual map stability then give the inequality by an epsilon limit. Degenerate and truncated costs are included. No compactness, finite support, distance moment, strict separation, general optimizer, or general-cost equality is required or asserted."))),
                DescribeRole.Theorem)
        )));
}
