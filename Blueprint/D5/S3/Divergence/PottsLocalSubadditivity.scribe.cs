using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class PottsLocalSubadditivityDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Capacity(Formula channel) =>
        Seq(F.Id("C"), Underscore, Grp(D(2)), Open, channel, Close);

    public DocumentDefinition Create()
    {
        var q = F.Id("q");
        var a = F.Id("A");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var p = F.Id("P");
        var r = F.Id("Q");
        var e = F.Id("e");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var natural = Seq(Mathbb, Grp(F.Id("N")));
        var fused = Call("star", p, r);
        var estimate = Seq(
            D(0), Lt, e, Sp, Rightarrow, Sp,
            Capacity(p), Le, Sp, e, Sp, Rightarrow, Sp,
            Capacity(fused), Le, Sp,
            Open, D(1), Plus, a, Sp, e, Caret,
            Grp(Frac, Grp(D(1)), Grp(D(5))), Close, Sp,
            Open, Capacity(p), Plus, Capacity(r), Close);
        var channels = All("P", Call("FMSChannel", Call("Fin", q), y),
            All("Q", Call("FMSChannel", Call("Fin", q), z), All("e", real, estimate)));
        var type = Seq(Operatorname, Grp(F.Id("Type")));
        var alphabets = All("Y", type, All("Z", type, Seq(
            OpenBracket, Call("Fintype", y), CloseBracket, Sp,
            OpenBracket, Call("Fintype", z), CloseBracket, Comma, Sp, channels)));
        var statement = All("q", natural, Seq(
            D(2), Le, Sp, q, Sp, Rightarrow, Sp,
            Exists, Sp, a, Colon, Sp, real, Comma, Sp,
            D(0), Lt, a, Sp, Land, Sp, alphabets));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform local chi-square subadditivity for finite symmetric channels observing one input.",
            H("Local Chi-Square Subadditivity for Symmetric Channels"),
            Blocks(Describe.Lean(
                DescribeId.Create("uniform-local-symmetric-channel-fusion-bound"),
                DeclarationHandle.Create("D5/S3/Divergence/PottsLocalSubadditivity.fully_symmetric_fusion_bound"),
                H("A constant independent of the output alphabet sizes"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Entropy/gupolyanskiy2023potts")),
                Blocks(
                    Paragraph(Text(
                        "The input is uniform on Fin(q), with q at least two. An FMSChannel is a nonnegative real " +
                        "row-stochastic table P(i,y), together with a group homomorphism from input permutations " +
                        "to output permutations preserving its entries under the simultaneous action. The output " +
                        "alphabets Y and Z are arbitrary finite types. The variable e in the formula is a positive " +
                        "real error parameter.")),
                    Paragraph(Text(
                        "Write m_P(y) = q⁻¹ Σ_i P(i,y) and C₂(P) = q⁻¹ Σ_y (Σ_i P(i,y)²)/m_P(y) − 1. " +
                        "Real division gives 0/0 = 0. A zero output mass forces every entry in that column to be zero. " +
                        "The posterior on a zero column is assigned the uniform distribution; its weighted " +
                        "contribution remains zero. Thus zero entries, zero columns and redundant output symbols " +
                        "are included.")),
                    Paragraph(Text(
                        "The channel star(P,Q) has table P(i,y)Q(i,z). Its two outputs are conditionally independent " +
                        "given the same input i. The product of the two output permutation actions certifies its " +
                        "symmetry. Its capacity equals the finite posterior-mixture fusion expression, including " +
                        "pairs of posteriors with zero overlap.")),
                    Paragraph(Text(
                        "For a posterior p, the quadratic defect is q Σ_i p(i)² − 1. Permutation averaging cancels " +
                        "the first variation in the rational fusion expression. A centered sum of squares bounds " +
                        "the remaining overlap, giving a local square-root estimate. Splitting posterior mixtures " +
                        "at defect t² when their mean defect is at most t⁵ gives the fifth-root error. The choice " +
                        "A = 8q⁴ + q is positive and independent of both output alphabet sizes.")),
                    Paragraph(Text(
                        "This is the finite-output form of Gu and Polyanskiy's local subadditivity estimate " +
                        "(arXiv:2303.14688v2, Lemma 20; Appendix D.1, Lemma 35). It supplies a bound for combining " +
                        "weak symmetric observations. The broader conjectures on uniqueness, boundary irrelevance " +
                        "and global stability of belief propagation above the Kesten–Stigum threshold concern " +
                        "iterated tree dynamics and are separate conclusions."))),
                DescribeRole.Theorem))));
    }
}
