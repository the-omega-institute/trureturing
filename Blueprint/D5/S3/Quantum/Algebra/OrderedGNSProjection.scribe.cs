using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OrderedGNSProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful matrix states detect positivity through internal compressions of a star-subalgebra.",
        H("Ordered GNS Projections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("internal-compressions-detect-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions"),
                H("Internal compressions detect positivity"),
                StatementSource.FromAuthor(InternalPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an arbitrary positive definite complex matrix rho and a unital star-subalgebra A. "
                        + "A Hermitian matrix y in A is positive semidefinite if every compression q-star y q, "
                        + "with q in A, has nonnegative real rho-weighted trace.")),
                    Paragraph(Text(
                        "Continuous functional calculus keeps the square root of the negative part of y in A. "
                        + "Its compression is the negative of the square of that negative part. "
                        + "Faithfulness of the weighted matrix inner product forces the negative part to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-gns-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization"),
                H("Ordered comparisons and complete positivity"),
                StatementSource.FromAuthor(CharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be any positive definite complex matrix of trace one, and let A be any "
                        + "unital star-subalgebra on the same finite carrier. The map E is the unique "
                        + "orthogonal projection onto A for the inner product tr(rho x-star y). "
                        + "Its left ordered comparisons determine E without any positivity assumption.")),
                    Paragraph(Text(
                        "Retraction, preservation of the unit and state, and the left module law follow "
                        + "from that orthogonal projection. The additional complex identity "
                        + "tr(rho E(x) a) = tr(rho x a), for every a in A, holds exactly when E preserves "
                        + "adjoints. Conjugating the left module law then gives the right module law.")),
                    Paragraph(Text(
                        "For a positive input, bimodularity and state preservation make all internal "
                        + "compressions of its image nonnegative under the faithful state. The preceding "
                        + "positivity test therefore makes the image positive. At every finite matrix "
                        + "amplification the block algebra M_k(A), the entrywise map id tensor E, and the "
                        + "faithful density I_k tensor rho satisfy the same identities. This density "
                        + "evaluates a matrix as the sum of its diagonal-block states; for nonzero k, "
                        + "division by k gives the normalized amplified state and preserves the sign test. "
                        + "The empty amplification is included. Thus every actual PSD input has a PSD image.")),
                    Paragraph(Text(
                        "The resulting expectation is unital, completely positive, idempotent, state "
                        + "preserving and an A-bimodule map, with image exactly A. Conversely, its bimodule "
                        + "and state identities recover the original right ordered comparison. The "
                        + "equivalence concerns these three conditions; no modular-flow or block "
                        + "classification is asserted."))),
                DescribeRole.Theorem))));

    private static Formula StarOf(Formula value) => Seq(value, Caret, Grp(Star));
    private static Formula StateOf(Formula value) => Seq(
        Varphi, Underscore, Grp(Rho), Open, value, Close);

    private static Formula InternalPositivityFormula()
    {
        Formula y = F.Id("y");
        Formula q = F.Id("q");
        Formula a = F.Id("A");
        return Disp(Seq(
            Forall, Sp, y, InMacro, a, Comma, Sp,
            StarOf(y), Eq, y, Implies,
            Open, Forall, Sp, q, InMacro, a, Comma, Sp,
                Re, StateOf(Seq(StarOf(q), y, q)), Geq, D(0), Close,
            Implies, y, Geq, D(0)));
    }

    private static Formula CharacterizationFormula()
    {
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula e = F.Id("E");
        Formula algebra = F.Id("A");
        Formula Apply(Formula value) => Seq(e, Open, value, Close);
        Formula right = Seq(Open, Forall, Sp, x, Comma, Sp,
            Forall, Sp, a, InMacro, algebra, Comma, Sp,
            StateOf(Seq(Apply(x), a)), Eq, StateOf(Seq(x, a)), Close);
        return Disp(Seq(
            right, Iff,
            Open, Forall, Sp, x, Comma, Sp, Apply(StarOf(x)), Eq, StarOf(Apply(x)), Close,
            Iff, Call("Expectation", Rho, algebra, e)));
    }
}
