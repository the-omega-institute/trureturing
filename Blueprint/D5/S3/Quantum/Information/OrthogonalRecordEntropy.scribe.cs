using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class OrthogonalRecordEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/OrthogonalRecordEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal fragment records retain the entire classical entropy of a pointer "
            + "distribution, conditional on the supplied record structure.",
        H("Orthogonal Records and Pointer Information"),
        Blocks(
            Paragraph(Text(
                "Let p be any finite probability distribution and rho_i any fragment density "
                    + "states. The physical hypothesis is explicit: rho_i rho_j = 0 for i != j. "
                    + "No observer assumption is claimed to imply this record structure. "
                    + "Zero weights and singular density states are allowed.")),
            Result("orthogonal-mixture", "orthogonal_mixture_entropy",
                "Entropy of an orthogonal mixture",
                "For the mixture sum_i p_i rho_i, its von Neumann entropy equals H(p) plus "
                    + "sum_i p_i S(rho_i). WeightedEntropy denotes that latter finite sum. "
                    + "Orthogonal positive operators are the positive and negative parts of "
                    + "their difference. Functional calculus and the scalar product identity "
                    + "for negative x log x give the decomposition.",
                Disp(Seq(Call("Orthogonal", Rho), Sp, Rightarrow, Sp,
                    Call("S", Call("mixture", F.Id("p"), Rho)), Sp, Eq, Sp,
                    Call("H", F.Id("p")), Sp, Plus, Sp,
                    Call("WeightedEntropy", F.Id("p"), Rho)))),
            Result("pointer-information", "orthogonal_record_trace_gives_sbs_consensus",
                "The fragment carries all pointer information",
                "The joint state is sum_i p_i |i><i| tensor rho_i. Its system marginal is "
                    + "the diagonal pointer distribution and its fragment marginal is the "
                    + "mixture. Both marginals are computed by partial trace. Applying the "
                    + "entropy decomposition to the joint state and fragment gives I = H(p). "
                    + "This equality is the information content of the conditional result; "
                    + "measurement instruments and multi-observer protocols are outside scope.",
                Disp(Seq(Call("Orthogonal", Rho), Sp, Rightarrow, Sp,
                    Call("quantumMutualInformation", Call("recordState", F.Id("p"), Rho)),
                    Sp, Eq, Sp, Call("H", F.Id("p"))))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/le2019orthogonalrecords")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
