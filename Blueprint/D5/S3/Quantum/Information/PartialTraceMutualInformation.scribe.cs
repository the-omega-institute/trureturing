using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PartialTraceMutualInformationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/PartialTraceMutualInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial traces give density-state marginals, and independent product states have "
            + "zero quantum mutual information.",
        H("Partial Trace and Quantum Mutual Information"),
        Blocks(
            Result("left-positive", "partialTraceLeft_posSemidef",
                "Tracing out the left factor preserves positivity",
                "For arbitrary finite carriers A and B, the reduced matrix is a finite sum "
                    + "of principal submatrices.", PositivityFormula("partialTraceLeft")),
            Result("right-positive", "partialTraceRight_posSemidef",
                "Tracing out the right factor preserves positivity",
                "The same principal-submatrix argument applies to the other factor.",
                PositivityFormula("partialTraceRight")),
            Result("left-trace", "trace_partialTraceLeft",
                "The left partial trace preserves trace",
                "For every joint matrix, summing the reduced diagonal recovers its diagonal sum.",
                TraceFormula("partialTraceLeft")),
            Result("right-trace", "trace_partialTraceRight",
                "The right partial trace preserves trace",
                "Together with positivity, trace preservation gives a normalized marginal.",
                TraceFormula("partialTraceRight")),
            Describe.Lean(
                DescribeId.Create("mutual-information"),
                DeclarationHandle.Create(Module + "quantumMutualInformation"),
                H("Mutual information of a joint density state"),
                StatementSource.FromAuthor(MutualInformationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The only input is the joint state. marginalRight retains A and "
                    + "marginalLeft retains B; each is constructed by partial trace."))),
                DescribeRole.Definition),
            Result("product-entropy", "vonNeumannEntropy_productState",
                "Entropy adds on independent product states",
                "The spectrum of the product is the multiset of pairwise eigenvalue products. "
                    + "For any two density states on finite carriers, including singular states, "
                    + "the proof uses the zero value of x log x at zero.", ProductEntropyFormula()),
            Result("product-information", "quantumMutualInformation_productState",
                "Independent product states have zero mutual information",
                "The actual partial traces recover the two factors. Their entropies cancel "
                    + "the entropy of the product by tensor additivity.", ProductInformationFormula()))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/blore2026partialtrace")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula PositivityFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("PosSemidef", F.Id("M")), Sp, Rightarrow, Sp,
        Call("PosSemidef", Call(partialTrace, F.Id("M")))));

    private static Formula TraceFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("trace", Call(partialTrace, F.Id("M"))), Sp, Eq, Sp,
        Call("trace", F.Id("M"))));

    private static Formula MutualInformationFormula() => Disp(Seq(
        Call("quantumMutualInformation", Rho), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Call("marginalRight", Rho)), Sp, Plus, Sp,
        Call("vonNeumannEntropy", Call("marginalLeft", Rho)), Sp, Minus, Sp,
        Call("vonNeumannEntropy", Rho)));

    private static Formula ProductEntropyFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("vonNeumannEntropy", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Rho), Sp, Plus, Sp,
        Call("vonNeumannEntropy", SigmaLower)));

    private static Formula ProductInformationFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("quantumMutualInformation", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Num(0)));
}
