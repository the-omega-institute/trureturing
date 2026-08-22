using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class CoarseGrainingCannotAddInformationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic coarse-graining preserves finite probability laws and cannot increase "
            + "mutual information.",
        H("Coarse-Graining Cannot Add Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-right-image-preserves-probability-laws"),
                DeclarationHandle.Create(DeclarationPrefix + "deterministicRight_is_law"),
                H("A deterministic right-coordinate image preserves probability laws"),
                StatementSource.FromAuthor(DeterministicRightLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Start with a normalized nonnegative mass function on A times B and send "
                        + "only its B-coordinate through a deterministic map f. The mass at "
                        + "(a,d) is the sum of p(a,b) over the fiber f(b)=d, so it remains "
                        + "nonnegative. Summing over d counts every b exactly once and preserves "
                        + "total mass one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "deterministic-right-processing-cannot-increase-information"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mutual_information_deterministic_right_le"),
                H("Deterministic right-coordinate processing cannot increase information"),
                StatementSource.FromAuthor(DeterministicRightInformationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The map f defines the deterministic channel W(b,d)=1 when f(b)=d and "
                            + "zero otherwise. Coupling this channel to p gives a normalized "
                            + "Markov law A to B to D whose A-B marginal is p and whose A-D "
                            + "marginal is the deterministic right-coordinate image.")),
                    Paragraph(Text(
                        "Markov data processing therefore bounds the mutual information between "
                            + "A and f(B) by that between A and B. The result applies to every "
                            + "map f; no injectivity or surjectivity is required."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("coarse-graining-cannot-add-information"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "coarse_graining_cannot_add_information"),
                H("Coarse-graining both states cannot add mutual information"),
                StatementSource.FromAuthor(CoarseGrainingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the same deterministic concept map to both coordinates of a "
                            + "finite joint law. Processing the second coordinate first cannot "
                            + "increase mutual information. Coordinate-swap symmetry then turns "
                            + "processing the first coordinate into a second application of the "
                            + "same one-coordinate data-processing bound.")),
                    Paragraph(Text(
                        "The resulting law is exactly the fiber-sum coarseGrainedJoint: each "
                            + "coarse pair receives all microscopic mass mapped to it. Thus the "
                            + "mutual information between consecutive coarse states is at most "
                            + "the mutual information between the original microscopic states."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula FintypeInstance(Formula type) =>
        Seq(
            OpenBracket,
            Operatorname,
            Grp(F.Id("Fintype")),
            Open,
            type,
            Close,
            CloseBracket);

    private static Formula ProbabilityLaw(Formula law) =>
        Seq(Operatorname, Grp(F.Id("ProbabilityLaw")), Open, law, Close);

    private static Formula MutualInformation(Formula law) =>
        Seq(Operatorname, Grp(F.Id("mutualInformation")), Open, law, Close);

    private static Formula DeterministicRight(Formula law, Formula map) =>
        Call("deterministicRight", law, map);

    private static Formula CoarseGrainedJoint(Formula law, Formula map) =>
        Call("coarseGrainedJoint", law, map);

    private static Formula DeterministicRightLawFormula()
    {
        Formula typeA = F.Id("A");
        Formula typeB = F.Id("B");
        Formula typeD = F.Id("D");
        Formula law = F.Id("p");
        Formula map = F.Id("f");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, typeA, Comma, Sp, typeB, Comma, Sp, typeD,
            Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            FintypeInstance(typeA), Sp, FintypeInstance(typeB), Sp,
            FintypeInstance(typeD), Comma, RowBreak,
            law, Colon, Sp, Arrow(Product(typeA, typeB), RealNumbers()), Comma, Sp,
            map, Colon, Sp, Arrow(typeB, typeD), Comma, RowBreak,
            ProbabilityLaw(law), Sp, Rightarrow, Sp,
            ProbabilityLaw(DeterministicRight(law, map)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DeterministicRightInformationFormula()
    {
        Formula typeA = F.Id("A");
        Formula typeB = F.Id("B");
        Formula typeD = F.Id("D");
        Formula law = F.Id("p");
        Formula map = F.Id("f");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, typeA, Comma, Sp, typeB, Comma, Sp, typeD,
            Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            FintypeInstance(typeA), Sp, FintypeInstance(typeB), Sp,
            FintypeInstance(typeD), Comma, RowBreak,
            law, Colon, Sp, Arrow(Product(typeA, typeB), RealNumbers()), Comma, Sp,
            map, Colon, Sp, Arrow(typeB, typeD), Comma, RowBreak,
            ProbabilityLaw(law), Sp, Rightarrow, Sp,
            MutualInformation(DeterministicRight(law, map)), Sp, Leq, Sp,
            MutualInformation(law), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CoarseGrainingFormula()
    {
        Formula microscopic = F.Id("X");
        Formula coarse = F.Id("C");
        Formula law = F.Id("p");
        Formula map = F.Id("c");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, microscopic, Comma, Sp, coarse,
            Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            FintypeInstance(microscopic), Sp, FintypeInstance(coarse), Comma, RowBreak,
            law, Colon, Sp,
            Arrow(Product(microscopic, microscopic), RealNumbers()), Comma, Sp,
            map, Colon, Sp, Arrow(microscopic, coarse), Comma, RowBreak,
            ProbabilityLaw(law), Sp, Rightarrow, Sp,
            MutualInformation(CoarseGrainedJoint(law, map)), Sp, Leq, Sp,
            MutualInformation(law), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
