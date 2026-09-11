using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class InputInformationBalanceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/InputInformationBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The information shared by a reference with two complementary outputs sums to twice "
            + "the reference entropy when the joint state is pure.",
        H("Input Information Balance"),
        Blocks(
            Paragraph(Text("All carriers are finite. IsPure means that the density matrix "
                + "is the outer product of one amplitude vector with its conjugate. "
                + "Normalization and positivity belong to DensityState.")),
            Result("complementary-entropy", "pure_complementary_entropy",
                "Complementary marginals have equal entropy",
                "For a pure state on A times B, the coefficient matrix gives the two "
                    + "marginals as rectangular Gram products, with one transposed. "
                    + "Their nonzero eigenvalues agree with multiplicity; zero eigenvalues "
                    + "contribute zero to entropy.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, Call("IsPure", Rho), Sp, Rightarrow, Sp,
                    S(Call("marginalLeft", Rho)), Sp, Eq, Sp,
                    S(Call("marginalRight", Rho))))),
            Paragraph(Text("For a global state on A times (B times R), stateAB traces out R "
                + "after regrouping as (A times B) times R. stateAR traces out B after "
                + "regrouping as (A times R) times B. The proof identifies the A marginals "
                + "of both states with marginalRight of the global state, and identifies "
                + "their B and R marginals with the corresponding complementary cuts.")),
            Result("information-balance", "input_information_balance",
                "The input information balance",
                "Purity gives S(AR) = S(B) and S(AB) = S(R). Expanding I(A:R) and I(A:B) "
                    + "cancels the B and R entropy terms, leaving twice S(A). The theorem "
                    + "takes the final pure joint state as input, including pure states "
                    + "obtained from a pure input and reference by an isometry.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, Call("IsPure", Rho), Sp, Rightarrow, Sp,
                    Call("quantumMutualInformation", Call("stateAR", Rho)), Sp, Plus, Sp,
                    Call("quantumMutualInformation", Call("stateAB", Rho)), Sp, Eq, Sp,
                    Num(2), Sp, S(Call("marginalRight", Rho))))))));

    private static Formula S(Formula state) => Call("vonNeumannEntropy", state);

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/meiburg2025purecomplement")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);
}
