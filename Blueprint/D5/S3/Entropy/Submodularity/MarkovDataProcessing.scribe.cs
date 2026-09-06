using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class MarkovDataProcessingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite Markov chain X to Y to Z, observing the channel output Z cannot reveal " +
            "more about X than observing the intermediate variable Y.",
        H("Markov Data Processing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-mutual-information-zero-iff-conditional-product"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MarkovDataProcessing."
                        + "conditional_mutual_information_eq_zero_iff_conditional_product"),
                H("Zero conditional mutual information is conditional factorization"),
                StatementSource.FromAuthor(ConditionalProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a normalized nonnegative law on I times (K times M), conditional "
                            + "mutual information is zero exactly when every conditioning slice "
                            + "of nonzero marginal mass is a product law.")),
                    Paragraph(Text(
                        "The right-hand marginal is formed after swapping the two coordinates "
                            + "of the conditional slice. Zero-mass slices are excluded by the "
                            + "explicit marginal hypothesis, and the conclusion is a function "
                            + "equality on K times M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mutual-information-gap-is-a-conditional-information-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_gap_eq_conditional_gap"),
                H("The mutual-information gap is a conditional-information gap"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Minus, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Eq, Sp,
                    Operatorname, Grp(F.Id("conditionalMutualInformation")), Open,
                    Operatorname, Grp(F.Id("zFirstLaw")), Open, F.Id("p"), Close, Close,
                    Minus, Sp,
                    Operatorname, Grp(F.Id("conditionalMutualInformation")), Open,
                    Operatorname, Grp(F.Id("yFirstLaw")), Open, F.Id("p"), Close, Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every pointwise nonnegative three-variable mass function, the " +
                        "difference I(X;Y) minus I(X;Z) equals I(X;Y given Z) minus I(X;Z " +
                        "given Y). The two conditional terms are represented by pivoting the " +
                        "right-nested law so that Z and Y respectively become the first, " +
                        "conditioning coordinate.")),
                    Paragraph(Text(
                        "This is the general algebraic pin: normalization is not required. " +
                        "Expanding mutual information and conditional mutual information into " +
                        "entropy defects leaves only entropy invariance under the two coordinate " +
                        "pivots and the four projection identities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("channel-generated-laws-satisfy-the-markov-interface"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MarkovDataProcessing.markov_of_channel"),
                H("Channel-generated laws satisfy the Markov interface"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Open, Forall, Sp, F.Id("y"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("z")), Sp,
                    F.Id("W"), Open, F.Id("y"), Comma, Sp, F.Id("z"), Close,
                    Eq, Sp, D(1), Close, Sp, Rightarrow, RowBreak,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    F.Id("z"), Comma, Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close,
                    Times, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("Y")), Open, F.Id("y"), Close,
                    Eq, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Open,
                    F.Id("x"), Comma, Sp, F.Id("y"), Close, Times, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("YZ")), Open,
                    F.Id("y"), Comma, Sp, F.Id("z"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p(x,y,z) be generated as pXY(x,y) times W(y,z), where each row " +
                        "of W sums to one. Summing out Z recovers pXY, while the Y and YZ " +
                        "marginals share the same sum over X. These identities prove the exact " +
                        "cross-multiplied Markov interface used by the subsequent theorems.")),
                    Paragraph(Text(
                        "No positivity or normalization assumption on pXY is needed for this " +
                        "algebraic witness. Thus the data-processing theorem's Markov hypothesis " +
                        "is verified for every row-normalized channel construction rather than " +
                        "silently assuming the desired conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markov-mutual-information-data-processing"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_le_of_markov"),
                H("Markov mutual information obeys data processing"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Leq, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a normalized nonnegative law satisfying the X to Y to Z Markov " +
                        "interface, the conditional mutual information I(X;Z given Y) vanishes " +
                        "by the conditional-product equality characterization. The gap identity " +
                        "then identifies I(X;Y) minus I(X;Z) with I(X;Y given Z).")),
                    Paragraph(Text(
                        "Conditional mutual information is nonnegative for the Z-pivoted law, " +
                        "so that remaining gap is nonnegative. Therefore the channel output Z " +
                        "retains no more mutual information about X than the intermediate Y."))),
                DescribeRole.Theorem))));

    private static Formula ConditionalProductFormula()
    {
        Formula firstType = F.Id("I");
        Formula secondType = F.Id("K");
        Formula thirdType = F.Id("M");
        Formula law = F.Id("p");
        Formula point = F.Id("x");
        Formula index = F.Id("i");
        Formula pair = F.Id("q");
        Formula swapped = F.Id("r");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula productType = Seq(firstType, Sp, Times, Sp,
            Parenthesized(Seq(secondType, Sp, Times, Sp, thirdType)));
        Formula sliceType = Seq(secondType, Sp, Times, Sp, thirdType);
        Formula conditional = Call("conditional", law, index);
        Formula swappedConditional = Parenthesized(Seq(
            swapped, Colon, Sp, Seq(thirdType, Sp, Times, Sp, secondType), Sp,
            Mapsto, Sp,
            Call("conditional", law, index,
                Parenthesized(Seq(Call("snd", swapped), Comma, Sp, Call("fst", swapped))))));
        Formula productSlice = Parenthesized(Seq(
            pair, Colon, Sp, sliceType, Sp, Mapsto, Sp,
            Call("marginal", conditional, Call("fst", pair)), Sp, Times, Sp,
            Call("marginal", swappedConditional, Call("snd", pair))));
        Formula lawHypothesis = Parenthesized(Seq(
            Parenthesized(Seq(
                Forall, Sp, point, Colon, Sp, productType, Comma, Sp,
                D(0), Sp, Leq, Sp, Call("p", point))),
            Sp, Land, Sp,
            Sum, Underscore, Grp(point), Sp, Call("p", point), Sp, Eq, Sp, D(1)));
        Formula factorization = Seq(
            Forall, Sp, index, Colon, Sp, firstType, Comma, Sp,
            Call("marginal", law, index), Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            conditional, Sp, Eq, Sp, productSlice);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, firstType, Comma, Sp, secondType, Comma, Sp, thirdType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Call("Fintype", firstType), CloseBracket, Sp,
            OpenBracket, Call("Fintype", secondType), CloseBracket, Sp,
            OpenBracket, Call("Fintype", thirdType), CloseBracket, Comma, RowBreak, Grp(),
            law, Colon, Sp, new Formula.TypeArrow(productType, real), Comma, Sp,
            lawHypothesis, Sp, Rightarrow, RowBreak, Grp(),
            Call("conditionalMutualInformation", law), Sp, Eq, Sp, D(0),
            Sp, Iff, Sp, Parenthesized(factorization), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
