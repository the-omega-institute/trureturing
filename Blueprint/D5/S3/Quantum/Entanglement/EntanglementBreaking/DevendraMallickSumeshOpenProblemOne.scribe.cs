using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class DevendraMallickSumeshOpenProblemOneDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Resource/devendra2023mapping");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 2-entanglement-breaking map on complex matrices can be indecomposable.",
        H("Decomposability of 2-entanglement-breaking maps"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim"),
                H("The universal decomposability assertion"), StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Open Problem 1, arXiv:2105.14991v2, p. 26: “Is every 2-EB map Φ : 𝕄₍d₁₎ → 𝕄₍d₂₎ decomposable?” The input and output dimensions are independently quantified in the positive naturals Npos. MatrixMap(a,b) is the type of complex-linear maps from the full a by a complex matrix algebra to the full b by b complex matrix algebra."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-devendramallicksumesh-openproblem1-counterexample"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_counterexample"),
                H("An indecomposable 2-entanglement-breaking map"), StatementSource.FromAuthor(F.Disp(Counterexample())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Taking k equal to two and both dimensions equal to 4194304 gives a 2-entanglement-breaking map that admits no decomposition into a completely positive and a completely copositive map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-devendramallicksumesh-openproblem1-refuted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted"),
                H("Refutation of universal decomposability"), StatementSource.FromAuthor(F.Disp(
                    new Formula.Not(new Formula.NamedConstant(FormulaIdentifier.Create("claim"))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The square counterexample belongs to the class quantified by the universal assertion and violates its conclusion."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("devendra-mallick-sumesh-2023-open-problem-1"),
                    ResolutionKind.Refuted)))));

    private static Formula PositiveNaturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Npos"));

    private static Formula Claim() => Bind(FormulaQuantifier.ForAll, "a", PositiveNaturals(),
        Bind(FormulaQuantifier.ForAll, "b", PositiveNaturals(),
            Bind(FormulaQuantifier.ForAll, "f", Map(F.Id("a"), F.Id("b")),
                new Formula.Logic(KEB(), FormulaLogicOperator.Implies, Decomposable()))));

    private static Formula Counterexample() => Bind(FormulaQuantifier.Exists, "d", PositiveNaturals(),
        Bind(FormulaQuantifier.Exists, "f", Map(F.Id("d"), F.Id("d")),
            new Formula.Logic(KEB(), FormulaLogicOperator.And, new Formula.Not(Decomposable()))));

    private static Formula Map(Formula a, Formula b) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("MatrixMap"), [a, b]);

    private static Formula KEB() =>
        new Formula.FunctionCall(FormulaIdentifier.Create("IsKEB"), [F.D(2), F.Id("f")]);

    private static Formula Decomposable() =>
        new Formula.FunctionCall(FormulaIdentifier.Create("IsDecomposable"), [F.Id("f")]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
}
