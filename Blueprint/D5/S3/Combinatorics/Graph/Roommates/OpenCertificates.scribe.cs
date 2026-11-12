using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class OpenCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable partial matchings and the Mertens range-two probability estimate.",
        H("OpenCertificates"), Blocks(
            Describe.Lean(DescribeId.Create("rank-injective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.rank_injective"),
                H("rank_injective"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a ranking permutation and nonzero integer offsets a and b between -2 and 2, equality of offsetRank implies a=b. The paired-certificate construction uses this injectivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("offsetrank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.offsetRank"),
                H("offsetRank"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.Certificate"),
                H("Certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certifiedword"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.CertifiedWord"),
                H("CertifiedWord"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count"),
                H("count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate-restrict"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.certificate_restrict"),
                H("certificate_restrict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-submultiplicative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_submultiplicative"),
                H("count_submultiplicative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-lower"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_lower"),
                H("count_lower"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exclusivetriangle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.ExclusiveTriangle"),
                H("ExclusiveTriangle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exclusive-triangle-not-certified"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified"),
                H("exclusive_triangle_not_certified"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicClosure supplies both cyclic comparisons; the exclusive-triangle count gives the strict bound, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trianglecount-reflection"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "reflectWord"),
                H("Interval reflection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reflection reverses the three interval positions and negates every signed offset. The certificate transport retains all integer-target injectivity constraints, including exterior targets, reciprocity and nonblocking. Zero remains single with rank four."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trianglecount-words"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "forbiddenWord"),
                H("Sixteen ranking words"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index is one orientation bit and three independent Boolean choices. In the forward orientation, positions zero, one and two respectively prefer signed offsets (1,2), (1,-1) and (-2,-1), in that order, to both exterior offsets. Each Boolean chooses the order of the bottom two offsets. Reflection gives the other orientation. The sixteen ranking words are distinct."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trianglecount-impossible"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "forbidden_not_certified"),
                H("Every listed profile is impossible"), StatementSource.FromAuthor(Disp(
                    TriangleCountAll("s", TriangleCountCall("TriangleIndex"), Seq(Neg, Sp, TriangleCountSome("d", TriangleCountCall("Assignments"),
                        TriangleCountCall("Certificate", TriangleCountCall("forbiddenWord", F.Id("s")), F.Id("d"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("TriangleIndex abbreviates Bool times (Fin 3 to Bool), and Assignments abbreviates Fin 3 to the integers. The forward case applies exclusive_triangle_not_certified. The reverse case transports a hypothetical certificate through reflection and applies the same theorem. No matching witness is enumerated; exterior partners and singles remain allowed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trianglecount-profiles"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "forbiddenProfiles"),
                H("Removed profiles"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite set is the image of forbiddenWord over its complete sixteen-element index type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trianglecount-cardinality"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "forbidden_card"),
                H("Exact removal cardinality"), StatementSource.FromAuthor(Disp(new Formula.Relation(
                    TriangleCountCall("card", TriangleCountCall("forbiddenProfiles")), FormulaRelationOperator.Equal, D(1,6)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The rank of offset 1 at the middle position recovers the orientation: it is zero forward and one after reflection. After undoing reflection, ranks at coordinates 2, 1 and 0 of positions 0, 1 and 2 respectively recover the three exterior-order bits. This word-level injection proves that precisely sixteen ranking profiles are removed, without enumerating all pairs of profiles."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trianglecount-count"), DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates." + "count_three_bound"),
                H("Three-site count bound"), StatementSource.FromAuthor(Disp(new Formula.Relation(
                    TriangleCountCall("count", D(3)), FormulaRelationOperator.LessThanOrEqual, D(1,3,8,0,8)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The map sends each existentially certified word to its underlying ranking word in the complement of the sixteen forbidden profiles. It is injective on words. The whole space has 24 cubed = 13824 elements; complement cardinality gives 13824 minus 16 = 13808. GrowthTransfer.result uses this bound to obtain strict exponential growth below 24. The source model is credited to The Formal Conjectures Authors under Apache-2.0."))), DescribeRole.Theorem))));

    private static Formula TriangleCountCall(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula TriangleCountAll(string name, Formula type, Formula body) => Seq(Forall, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
    private static Formula TriangleCountSome(string name, Formula type, Formula body) => Seq(Exists, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
}
