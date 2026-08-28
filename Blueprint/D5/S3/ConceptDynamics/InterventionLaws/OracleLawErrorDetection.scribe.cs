using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class OracleLawErrorDetectionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionLaws/OracleLawErrorDetection."
            + "oracle_intervention_law_error_detection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact intervention-law codewords decode uniquely below half their minimum "
            + "coordinate distance.",
        H("Oracle Intervention-Law Error Detection"),
        Blocks(Describe.Lean(
            DescribeId.Create("oracle-intervention-law-errors-have-a-unique-decoding"),
            DeclarationHandle.Create(Declaration),
            H("Oracle intervention-law errors have a unique decoding"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite law suite sends each model to its canonical jointReadout "
                        + "codeword. Its minimum distance is constructed as the least Hamming "
                        + "distance between codewords arising from distinct models.")),
                Paragraph(Text(
                    "If the received law word differs from the true model codeword in at most "
                        + "e coordinates, any competing codeword in the same radius lies within "
                        + "2e coordinates of it. The strict minimum-distance condition forces "
                        + "the competing codeword to equal the true one."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("Model");
        Formula lawType = F.Id("Law");
        Formula suiteSize = F.Id("n");
        Formula errorBudget = F.Id("e");
        Formula law = F.Id("law");
        Formula trueModel = F.Id("M");
        Formula received = F.Id("r");
        Formula candidate = F.Id("c");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula indexType = Call("Fin", suiteSize);
        Formula wordType = new Formula.TypeArrow(indexType, lawType);
        Formula lawFamilyType = new Formula.TypeArrow(
            indexType,
            new Formula.TypeArrow(modelType, lawType));
        Formula codeword = Call("jointReadout", law, trueModel);
        Formula code = Call("range", Call("jointReadout", law));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, modelType, Comma, Sp, lawType, Colon, Sp, type, Comma),
            Seq(
                Grp(), OpenBracket, Call("DecidableEq", lawType), CloseBracket, Comma),
            Seq(
                suiteSize, Comma, Sp, errorBudget, Sp, InMacro, Sp, naturals, Comma),
            Seq(
                law, Colon, Sp, lawFamilyType, Comma),
            Seq(
                trueModel, Colon, Sp, modelType, Comma, Sp,
                received, Colon, Sp, wordType, Comma),
            Seq(
                HammingDistance(received, codeword), Sp, Leq, Sp, errorBudget,
                Sp, Land, Sp,
                D(2), Sp, Times, Sp, errorBudget, Sp, Lt, Sp,
                Call("interventionMinimumDistance", law), Sp, Rightarrow),
            Seq(
                Exists, Sp, Bang, Sp, candidate, Colon, Sp, wordType, Comma),
            Seq(
                candidate, Sp, InMacro, Sp, code, Sp, Land, Sp,
                HammingDistance(received, candidate), Sp, Leq, Sp, errorBudget, Dot),
        ]));
    }

    private static Formula HammingDistance(Formula first, Formula second) =>
        Call("hammingDist", first, second);
}
