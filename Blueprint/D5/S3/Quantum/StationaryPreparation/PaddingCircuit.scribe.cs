using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingCircuitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual padding evolves through a blank initialized circuit using one fixed unitary at every step.",
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
                    "fixed unitary on A times K. Write const(U) for the constant family sending " +
                    "every natural time index to this same U. Let a be a multiset of A, and let r " +
                    "assign a memory vector to every multiset of A, with r(0)=f. Assume that for " +
                    "every nonzero b<=a and every i and k, applying U to the blank memory state " +
                    "r(b) gives r(b.erase(i))(k) in coordinate (i,k) when i occurs in b, and " +
                    "zero otherwise. For every n and starting time t, every b<=a with b.card=n, " +
                    "every word w of length n, and every memory coordinate k, the circuit " +
                    "coefficient is f(k) when occupation(w)=b and zero otherwise.")),
                Paragraph(Text(
                    "The same U is used at every step, independently of the starting time. The proof " +
                    "peels the first physical slot, applies the residual transition rule, and " +
                    "inducts on the remaining word length. The empty word is the initialized " +
                    "blank state, and each nonempty word reduces to its tail."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula n = F.Id("n"), t = F.Id("t"), b = F.Id("b");
        Formula w = F.Id("w"), k = F.Id("k"), blank = F.Id("blank");
        Formula circuit = Call("circuit", Call("const", F.Id("U")), n, t,
            Call("initialized", blank, n, Call("r", b)), Call("pair", w, k));
        return Disp(Seq(
            circuit, Sp, Eq, Sp,
            Call("if", Equal(Call("occupation", w), b), Call("f", k), D(0))));
    }
}
