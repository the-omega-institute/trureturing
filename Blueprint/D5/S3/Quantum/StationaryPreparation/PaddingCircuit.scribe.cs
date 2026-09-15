using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingCircuitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual padding evolves through one common blank initialized circuit.",
        H("Padding Circuit"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-circuit-output"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingCircuit.circuit_output_of_residuals"),
            H("Residual circuit coefficients"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A and K be finite types, let blank be a symbol of A, and let U be a " +
                    "unitary on A times K. Suppose r assigns a memory vector to each submultiset " +
                    "of a, with r(0)=f. If one application of U to the blank memory state " +
                    "r(b) produces r(b.erase(i)) in coordinate i whenever i occurs in b, and " +
                    "produces zero otherwise, then the length-n circuit coefficient on a word w " +
                    "and memory coordinate k is f(k) exactly when occupation(w)=b.")),
                Paragraph(Text(
                    "The statement holds at every starting time and for every legal b. The proof " +
                    "peels the first physical slot, applies the residual transition rule, and " +
                    "inducts on the remaining word length. The empty word is the initialized " +
                    "blank state, and each nonempty word reduces to its tail."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula n = F.Id("n"), t = F.Id("t"), b = F.Id("b");
        Formula w = F.Id("w"), k = F.Id("k"), blank = F.Id("blank");
        Formula circuit = Call("circuit", Call("U", t), n, t,
            Call("initialized", blank, n, Call("r", b)), Call("pair", w, k));
        return Disp(Seq(
            circuit, Sp, Eq, Sp,
            Call("if", Equal(Call("occupation", w), b), Call("f", k), D(0))));
    }
}
