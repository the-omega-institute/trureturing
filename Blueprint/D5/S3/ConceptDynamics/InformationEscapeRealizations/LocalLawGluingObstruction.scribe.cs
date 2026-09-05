using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class LocalLawGluingObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three pulled-back pair laws realize a four-class gluing-obstruction kernel.",
        H("Local-Law Gluing Obstruction Realization"),
        Blocks(
            DefinitionNode("local-law-gluing-realization-definition", "localLawGluingRealization",
                "Concrete gluing realization",
                "The realization evaluates equality on the two adjacent pairs and inequality on the outer pair."),
            TheoremNode("local-law-gluing-realization",
                "compatible_local_laws_can_lack_global_state_realization",
                "Gluing realization equivalence", RealizationFormula(),
                "The equivalence translates the frozen set-image statement to the arena law without invoking the frozen theorem."),
            TheoremNode("local-law-gluing-partition-count",
                "compatible_local_laws_can_lack_global_state_partition_count",
                "Four kernel classes", PartitionFormula(),
                "Exhaustive evaluation of the concrete three-ADMIT image yields four signatures."),
            TheoremNode("local-law-gluing-private-pair",
                "compatible_local_laws_can_lack_global_state_private_pair",
                "Private pair separation", PrivatePairFormula(),
                "The compiled primitive bundle separates 000 from 001."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula statement, string explanation) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StateType() => Seq(
        F.Id("Bool"), Sp, Times, Sp, F.Id("Bool"), Sp, Times, Sp, F.Id("Bool"));

    private static Formula Projection(Formula value, params byte[] fields)
    {
        var items = new List<Formula> { value };
        foreach (var field in fields) items.AddRange([Dot, D(field)]);
        return Seq([.. items]);
    }

    private static Formula SetImage(Formula function, Formula set) =>
        Seq(function, Sp, Apos, Apos, Sp, set);

    private static Formula LocalStatement()
    {
        Formula same = F.Id("sameLaw");
        Formula different = F.Id("differentLaw");
        Formula state = F.Id("state");
        Formula first = Projection(state, 1);
        Formula middle = Projection(state, 2, 1);
        Formula last = Projection(state, 2, 2);
        Formula prodFst = Seq(F.Id("Prod"), Dot, F.Id("fst"));
        Formula prodSnd = Seq(F.Id("Prod"), Dot, F.Id("snd"));
        Formula compatibility = Seq(
            SetImage(prodSnd, same), Sp, Eq, Sp,
                SetImage(prodFst, same), Sp, Land, Sp,
            SetImage(prodFst, same), Sp, Eq, Sp,
                SetImage(prodFst, different), Sp, Land, Sp,
            SetImage(prodSnd, same), Sp, Eq, Sp,
                SetImage(prodSnd, different));
        Formula globalState = Seq(
            Exists, Sp, state, Colon, Sp, StateType(), Comma, Sp,
            Tuple(first, middle), Sp, InMacro, Sp, same, Sp, Land, Sp,
            Tuple(middle, last), Sp, InMacro, Sp, same, Sp, Land, Sp,
            Tuple(first, last), Sp, InMacro, Sp, different);
        return Seq(Open, compatibility, Close, Sp, Land, Sp,
            new Formula.Not(Grp(globalState)));
    }

    private static Formula RealizationFormula() => Disp(Seq(
        LocalStatement(), Sp, Iff, Sp,
        F.Id("localLawGluingArena"), Dot, F.Id("Law"), Sp,
        F.Id("localLawGluingRealization"), Dot));

    private static Formula PartitionFormula()
    {
        Formula realization = F.Id("localLawGluingRealization");
        Formula state = F.Id("state");
        Formula signature = Tuple(
            Seq(realization, Dot, F.Id("readout"), Sp, F.Id("admit01"), Sp, state),
            Seq(realization, Dot, F.Id("readout"), Sp, F.Id("admit12"), Sp, state),
            Seq(realization, Dot, F.Id("readout"), Sp, F.Id("admit02"), Sp, state));
        Formula image = Seq(
            F.Id("Finset"), Dot, F.Id("univ"), Dot, F.Id("image"), Open,
            LambdaLower, Sp, state, Colon, Sp, StateType(), Comma, Sp, signature, Close);
        return Disp(Seq(Open, image, Close, Dot, F.Id("card"), Sp, Eq, Sp, D(4), Dot));
    }

    private static Formula PrivatePairFormula() => Disp(Seq(
        new Formula.Not(Grp(Seq(
            F.Id("localLawGluingRealization"), Dot, F.Id("toPrimitiveBundle"), Dot,
            F.Id("agrees"), Sp,
            Tuple(F.Id("false"), F.Id("false"), F.Id("false")), Sp,
            Tuple(F.Id("false"), F.Id("false"), F.Id("true"))))), Dot));
}
