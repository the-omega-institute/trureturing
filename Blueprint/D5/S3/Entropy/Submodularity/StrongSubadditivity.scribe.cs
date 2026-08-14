using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class StrongSubadditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Shannon entropy is submodular for three variables, with equality exactly when the last two variables factor conditionally on every active first-coordinate slice.",
        H("Strong Subadditivity and Conditional Products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xy-projection-sums-out-the-third-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/StrongSubadditivity.xyProjection"),
                H("The XY projection sums out the third coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Open,
                    F.Id("x"), Comma, Sp, F.Id("y"), Close, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("z")), Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a mass function on the right-nested product X times (Y times Z), " +
                        "the XY projection sums over Z while retaining X and Y. The nesting is " +
                        "part of the interface because conditioning the original law on X must " +
                        "produce a joint law on Y times Z."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("xz-projection-sums-out-the-second-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/StrongSubadditivity.xzProjection"),
                H("The XZ projection sums out the second coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Open,
                    F.Id("x"), Comma, Sp, F.Id("z"), Close, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The XZ projection instead sums over Y. Both projections have the same " +
                        "first-coordinate marginal as the original law; their conditional laws " +
                        "are respectively the Y and Z marginals of the original conditional " +
                        "joint law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-entropy-is-subadditive-on-each-slice"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/StrongSubadditivity.conditionalEntropy_pair_le_add"),
                H("Conditional entropy is subadditive on each slice"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close,
                    Leq, Sp,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Plus, Sp,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a normalized nonnegative law, each slice with nonzero X marginal " +
                        "is a normalized joint law on Y times Z. Two-variable entropy " +
                        "subadditivity applies to that slice, and multiplication by its " +
                        "nonnegative X weight preserves the inequality.")),
                    Paragraph(Text(
                        "A zero-marginal slice contributes zero to all three conditional " +
                        "entropies. Summing the slicewise inequalities therefore gives the " +
                        "conditional form without imposing a positivity hypothesis on every " +
                        "first-coordinate marginal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-is-submodular-for-three-variables"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular"),
                H("Entropy is submodular for three variables"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("p"), Close, Plus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("X")), Close,
                    Leq, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XY")), Close,
                    Plus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Applying the entropy chain rule to the original law and to both " +
                        "two-coordinate projections converts conditional subadditivity into " +
                        "the classical strong-subadditivity inequality. The common marginal " +
                        "terms cancel algebraically.")),
                    Paragraph(Text(
                        "The statement uses the submodular arrangement H(X,Y,Z) plus H(X) at " +
                        "the left and H(X,Y) plus H(X,Z) at the right. All entropies are finite " +
                        "Shannon entropies in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equality-means-conditional-product-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular_eq_iff_conditional_product"),
                H("Equality means conditional product factorization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("H"), Open, F.Id("p"), Close, Plus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("X")), Close,
                    Eq, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XY")), Close,
                    Plus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XZ")), Close,
                    Sp, Leftrightarrow, RowBreak,
                    Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("X")), Open, F.Id("x"), Close,
                    Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("z"), Mid, Sp,
                    F.Id("x"), Close, Eq, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("Y")), Open,
                    F.Id("y"), Mid, Sp, F.Id("x"), Close, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("Z")), Open,
                    F.Id("z"), Mid, Sp, F.Id("x"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The difference between the two sides of conditional subadditivity is " +
                        "the sum over X of the slice weight times the mutual information of " +
                        "the conditional YZ law. Every summand is nonnegative on an active " +
                        "slice, so equality forces each such mutual information to vanish.")),
                    Paragraph(Text(
                        "Vanishing finite mutual information is equivalent to the conditional " +
                        "joint law being the product of its Y and Z marginals. Conversely, that " +
                        "factorization makes every active summand vanish. Zero-marginal slices " +
                        "are deliberately excluded because their conditional law is the " +
                        "artificial zero-over-zero law and contributes no entropy."))),
                DescribeRole.Theorem))));
}
