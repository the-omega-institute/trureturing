using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class PositiveSectionCentralSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive sections preserve central blocks", H("Positive sections preserve central blocks"),
        Blocks(Describe.Lean(DescribeId.Create("positive-section-central-support"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/PositiveSectionCentralSupport.positive_section_central_support"),
            H("A global section cannot create cross-central coherence"),
            StatementSource.FromAuthor(Disp(Claim())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let S and n be finite sets and let C(s) be finite matrix index sets, including empty sets. The coarse algebra is the direct sum of the complex matrices on C(s), represented as a dependent family. E and R are complex linear maps in opposite directions. The matrices Q(s) are Hermitian idempotents and their sum is identity. For every fine matrix B and every s, ordinary traces satisfy tr(Q(s) B) = tr((E B)(s)). The right inverse equation E(R(X)) = X holds for every coarse matrix family X. Positivity of R means that componentwise positive semidefinite inputs have positive semidefinite output. No complete positivity or trace-one restriction is assumed.")),
                Paragraph(Text("For every componentwise positive family rho, the conclusion is R(rho) = sum over s of Q(s) R(rho) Q(s). To prove it, insert rho(s) into one coarse block and zero into the others. Positivity gives a positive fine lift B(s). Every other projected trace is zero by trace duality and the global right inverse equation. A positive matrix with zero projected trace annihilates that projection on both sides: compress it, use the zero-trace criterion for positive matrices, and then the zero quadratic-form criterion for each column. The identity partition therefore confines B(s) to Q(s). Linearity and summation over the old blocks give the conclusion.")),
                Paragraph(Text("For finite legal-prefix algebras with ordinary block traces, E is incoming-copy extraction and Q(s) is the image of the old central unit. A direct sum of fine matrices is represented inside the matrix algebra on the disjoint union of its bases; extraction discards cross-fine-block entries. This correspondence retains zero-dimensional old blocks and the initial layer. The conclusion concerns every global linear positive right inverse. A coherent lift of one selected coarse state need not be the output of such a right inverse. Coherence among multiplicity copies within one old central block is compatible with the conclusion; no classification of those sections is asserted here."))),
            DescribeRole.Theorem))));
    private static Formula Claim()
    {
        Formula result = Rel(Call("Apply", F.Id("R"), F.Id("rho")), Eq,
            Call("CentralPinching", F.Id("Q"), Call("Apply", F.Id("R"), F.Id("rho"))));
        result = Rel(Conj(Call("HermitianIdempotents", F.Id("Q")),
            Call("SumIsIdentity", F.Id("Q")), Call("BlockTraceDuality", F.Id("E"), F.Id("Q")),
            Call("GlobalRightInverse", F.Id("E"), F.Id("R")), Call("Positive", F.Id("R")),
            Call("PositiveBlocks", F.Id("rho"))), Implies, result);
        result = All("rho", Call("BlockMatrices", F.Id("C")), result);
        result = All("Q", Call("MatrixFamily", F.Id("S"), F.Id("n")), result);
        result = All("R", Call("ComplexLinearSection", F.Id("C"), F.Id("n")), result);
        result = All("E", Call("ComplexLinearExtraction", F.Id("n"), F.Id("C")), result);
        result = Instance(Call("FiniteDecidableBlocks", F.Id("C")), result);
        result = All("C", Call("BlockIndexFamily", F.Id("S")), result);
        result = Instance(Call("DecidableEq", F.Id("n")), result);
        result = Instance(Call("Fintype", F.Id("n")), result);
        result = Instance(Call("DecidableEq", F.Id("S")), result);
        result = Instance(Call("Fintype", F.Id("S")), result);
        return All("S", Call("Type"), All("n", Call("Type"), result));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
