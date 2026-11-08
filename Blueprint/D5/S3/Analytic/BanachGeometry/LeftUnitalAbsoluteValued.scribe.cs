using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BanachGeometry;

internal sealed class LeftUnitalAbsoluteValuedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero left multiplication in a real Banach absolute-valued algebra.",
        H("Left units and division"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left-unital-absolute-valued-multiplier"),
                DeclarationHandle.Create("D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued.exists_left_multiplier_equiv"),
                H("Every nonzero left multiplier is invertible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a nonzero complete real normed vector space and m an arbitrary "
                        + "real bilinear multiplication on E. Suppose norm(m(x,y))=norm(x)norm(y) "
                        + "for every x,y, and m(e,y)=y for one e and every y. For every x not zero "
                        + "there exists a continuous real linear equivalence T whose value on "
                        + "each y is the same original product m(x,y). Its operator norm is norm(x), "
                        + "and its inverse operator norm is the reciprocal of norm(x). "
                        + "There is no associativity, right-unit, finite-dimensional, quadratic-norm "
                        + "or inner-product premise. Only x not zero is excluded; every y, "
                        + "including zero, remains in the original domain.")),
                    Paragraph(Text(
                        "Exact norm multiplicativity makes each nonzero multiplier injective. "
                        + "In rank one, finite dimension follows from that rank and injectivity "
                        + "gives surjectivity. In rank greater than one the punctured real space "
                        + "is connected. Invertible multipliers form an open set, by continuity "
                        + "of the operator family and Mathlib's Neumann perturbation theorem. "
                        + "They also form a closed set within the punctured space: a multiplier "
                        + "within half the limiting nonzero vector's norm has inverse norm "
                        + "the reciprocal of its own vector norm, so the same perturbation "
                        + "theorem inverts the limiting multiplier. The original left unit "
                        + "supplies a member, and connectedness propagates invertibility "
                        + "to every nonzero vector. Mathlib homothety identities give both "
                        + "exact operator norms.")),
                    Paragraph(Text(
                        "This is precisely the Banach-space inference in OmegaQ020 Lemma 3.3, "
                        + "source atom 29ed2981b018d6907b6e32cfb28541e5381f264c21324ce7190c551a824ecc1f. "
                        + "The source starts with the real vector space mathcal A and seminorm p; "
                        + "its null space is p inverse of zero and its quotient norm must be "
                        + "norm([a])=p(a). Constructing that exact quotient, descending the "
                        + "same multiplication and readable unit, and extending them to its "
                        + "completion remain separate obligations. This theorem applies to "
                        + "that completion only after those bridges have been proved. "
                        + "Original faithfulness is not extended to the completion.")),
                    Paragraph(Text(
                        "The remaining Euclidean-plane argument requires a complex Banach "
                        + "auxiliary norm preserving all real surjective similarity factors, "
                        + "the spectrum facts, and one spectral lambda for each x and nonzero y "
                        + "working for all real alpha,beta, including combinations equal to zero. "
                        + "The original p squared parallelogram law, its y=0 case and its pullback "
                        + "are not conclusions of this theorem. The full original Hopf, "
                        + "orientation, metric, connection and closed-loop clauses remain open. "
                        + "The auxiliary complex space is not the original physical J.")),
                    Paragraph(Text(
                        "The mathematical source attributes the absolute-valued algebra "
                        + "background to Rodriguez Palacios, One-sided division absolute valued "
                        + "algebras, Publicacions Matematiques 36(2B), 925-954. The result is "
                        + "a source formalization; no literature originality is claimed. "
                        + "Its faithful Reg source reconstruction is separate from a complete "
                        + "four-slot registration; any unfinished audit is tracked in issue 28177."))),
                DescribeRole.Theorem))));
}
