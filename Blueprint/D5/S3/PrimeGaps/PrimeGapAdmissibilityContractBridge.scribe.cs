using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class PrimeGapAdmissibilityContractBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct omission and local residue counts.",
        H("Direct omission and local residue counts"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-gap-admissibility-contract-bridge"),
            DeclarationHandle.Create("D5/S3/PrimeGaps/PrimeGapAdmissibilityContractBridge.directTupleAdmissible_iff_local_residue"),
            H("Direct omission and local residue counts"),
            StatementSource.FromAuthor(F.Disp(
                F.Seq(F.Forall, F.Sp, F.Id("H"), F.InMacro, F.Sp, Call("Finset", F.Id("Int")), F.Comma, Call("DirectTupleAdmissible", F.Id("H")), F.Iff, F.Grp(F.Forall, F.Sp, F.Id("p"), F.InMacro, F.Sp, F.Id("Nat"), F.Comma, Call("Prime", F.Id("p")), F.Rightarrow, Call("localResidueCount", F.Id("H"), F.Id("p")), F.Lt, F.Id("p"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This inherited equivalence applies to every finite integer offset set. The all-prime local count counts negated residue classes, while DirectTupleAdmissible asks for a missing direct residue. Negation identifies their cardinalities. No positivity assumption on H is needed."))),
            DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
