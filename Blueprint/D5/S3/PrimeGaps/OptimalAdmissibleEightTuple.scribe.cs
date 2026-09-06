using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class OptimalAdmissibleEightTupleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact admissible eight-tuple optimum.",
        H("The exact admissible eight-tuple optimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("optimal-admissible-eight-tuple"),
            DeclarationHandle.Create("D5/S3/PrimeGaps/OptimalAdmissibleEightTuple.minimalAdmissibleDiameter_eight_26"),
            H("The exact admissible eight-tuple optimum"),
            StatementSource.FromAuthor(F.Disp(
                new Formula.FunctionCall(FormulaIdentifier.Create("MinimalAdmissibleDiameter"), [F.D(8), F.D(2, 6)]))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("MinimalAdmissibleDiameter 8 26 asserts that an all-prime admissible natural eight-tuple exists in the width-26 window and that, for every natural C less than 26, no such tuple exists in the width-C window. The positive witness is {0,2,6,8,12,18,20,26}. The lower bound normalizes an arbitrary witness and applies a kernel-checked residue obstruction modulo 3, 5, and 7. This formalizes a standard numerical optimum and does not claim new number theory."))),
            DescribeRole.Theorem)),
        []));
}
