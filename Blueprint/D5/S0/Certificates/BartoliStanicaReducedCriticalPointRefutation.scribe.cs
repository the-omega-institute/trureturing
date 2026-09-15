using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class BartoliStanicaReducedCriticalPointRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bartoli2026apn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed reduced polynomial over F32 refutes the reduced critical-point conjecture.",
        H("Bartoli--Stănică Conjecture 2: reduced APN critical points"),
        Blocks(
            Paragraph(Text(
                "Bartoli and Stănică, Reduced polynomial lifts of APN permutations over "
                    + "Galois rings and effective non-APN bounds, arXiv:2608.30808v1 "
                    + "(31 August 2026), Conjecture 2 states: For every q = 2^m, the "
                    + "reduced representative f in F_(q)[x] of every APN permutation of "
                    + "F_(q) has a critical point in F_(q). The reduced representative "
                    + "means degree strictly less than q; the critical point is a finite "
                    + "rational a with the formal derivative f' evaluated at a equal to "
                    + "zero. This record keeps the universal quantifiers and does not "
                    + "use an unnormalized lift or an affine-invariance claim.")),
            Describe.Lean(
                DescribeId.Create("apn-differential-fiber-size"),
                DeclarationHandle.Create(Prefix + "differentialFiberSize"),
                H("Directional differential fiber size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite field K and Polynomial f, this is the cardinality of "
                        + "the fiber of x ↦ f(x+a)+f(x) at target b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("apn-exact-apn"),
                DeclarationHandle.Create(Prefix + "exactAPN"),
                H("Exact APN condition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The predicate requires every nonzero direction and every target "
                        + "to have a differential fiber of size at most two, together "
                        + "with one nonzero-direction target attaining size two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("apn-reduced-critical-point-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The reduced critical-point conjecture"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every m > 0, every finite characteristic-two field K with "
                        + "cardinality 2^m, and every Polynomial f over K of degree "
                        + "less than 2^m whose evaluation is bijective and whose exact "
                        + "APN predicate holds, the same field contains a with "
                        + "f.derivative.eval a = 0. The Lean definition uses the same "
                        + "polynomial in all hypotheses and in the derivative conclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("apn-reduced-critical-point-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The F32 reduced polynomial has no critical point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The theorem is a direct negation of the universal claim. Its "
                            + "live proof constructs the actual field with 32 elements "
                            + "and characteristic two from five-bit vectors reduced by "
                            + "t^5+t^2+1, then defines one degree-24 polynomial with the "
                            + "16 supplied nonzero coefficients. Kernel computation "
                            + "checks all 32 evaluations, the evaluation bijection, all "
                            + "31 × 32 nonzero-direction/target fibers, and the exact "
                            + "size-two fiber at direction label 1 and target label 16 "
                            + "with points 24 and 25.")),
                    Paragraph(Text(
                        "The same polynomial has nowhere-zero formal derivative on "
                            + "all 32 field elements. The degree bound is the reduced "
                            + "representative condition. Labels are binary vectors in "
                            + "the field model, not natural-number casts or ZMod 32. "
                            + "The result uses only propext, Classical.choice and "
                            + "Quot.sound in its axiom closure. This is a fixed finite "
                            + "refutation and makes no global priority claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "bartoli-stanica-reduced-critical-point-conjecture"),
                    ResolutionKind.Refuted)))));
}
