using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class StaticExactExperimentDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen static exact-design theorem realizes the typed two-CUT law.",
        H("Static Exact Experiment Design Realization"),
        Blocks(
            Definition("static-exact-concrete-realization", "staticExactExperimentRealization",
                "Concrete static exact-design realization",
                "The primitive realization assigns the change-X and change-Y Boolean response tables to the two CUT slots."),
            Node("static-exact-design-realization", "static_exact_design_realization",
                "Legacy realization equivalence",
                CertificateFormula(),
                "Both directions unfold the concrete experiment response table."),
            Node("static-exact-design-partition-count", "static_exact_design_partition_count",
                "Three kernel classes", PartitionCountFormula(),
                "The three model indices have three distinct two-bit signatures."),
            Node("static-exact-design-private-pair", "static_exact_design_private_pair",
                "Private pair separation",
                AgreesFormula(),
                "The change-X readout separates model zero from model one."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula CertificateFormula()
    {
        Formula model = F.Id("model");
        Formula experiment = F.Id("experiment");
        Formula selected = F.Id("selected");
        Formula changeX = F.Id("changeX");
        Formula changeY = F.Id("changeY");
        Formula finThree = Call("Fin", D(3));
        Formula response = Call("if", experiment, Apply(changeY, model), Apply(changeX, model));
        Formula individual = Seq(
            Forall, Sp, experiment, Colon, Sp, F.Id("Bool"), Comma, Sp,
            Neg, Sp, Call("Injective", Lambda(model, response)));
        Formula joint = Call("Injective", Call("jointReadout",
            Lambda(Seq(experiment, Colon, Sp, F.Id("Bool")),
                Call("if", experiment, changeY, changeX))));
        Formula selectedExperiment = F.Id("selectedExperiment");
        Formula selectedResponse = Call("if", Call("val", selectedExperiment),
            changeY, changeX);
        Formula selectedJoint = Call("Injective", Call("jointReadout",
            Lambda(Seq(selectedExperiment, Colon, Sp,
                    new Formula.SetBuilder(F.Id("candidate"), F.Id("candidate"), selected)),
                selectedResponse)));
        Formula minimal = Seq(
            Forall, Sp, selected, Colon, Sp, Call("Finset", F.Id("Bool")), Comma, Sp,
            selectedJoint, Sp, Implies, Sp,
            selected, Sp, Eq, Sp,
            new Formula.SetLiteral([F.Id("false"), F.Id("true")]));
        Formula statement = Seq(
            F.Id("let"), Sp, changeX, Eq,
            Lambda(Seq(model, Colon, Sp, finThree),
                Call("decide", Seq(model, Sp, Eq, Sp, D(1)))), Semi, Sp,
            changeY, Eq,
            Lambda(Seq(model, Colon, Sp, finThree),
                Call("decide", Seq(model, Sp, Eq, Sp, D(2)))), Semi, RowBreak, Grp(),
            Grp(individual), Sp, Land, RowBreak, Grp(),
            joint, Sp, Land, RowBreak, Grp(), Grp(minimal));
        Formula law = Seq(F.Id("staticExactExperimentArena"), Dot, F.Id("Law"),
            Open, F.Id("staticExactExperimentRealization"), Close);
        return Seq(Grp(statement), Sp, Iff, Sp, law);
    }

    private static Formula PartitionCountFormula()
    {
        Formula model = F.Id("model");
        Formula carrier = Call("Fin", D(3));
        Formula realization = F.Id("staticExactExperimentRealization");
        Formula firstIndex = Seq(Open, D(0), Colon, Sp, F.Id("StaticReadout"), Close);
        Formula secondIndex = Seq(Open, D(1), Colon, Sp, F.Id("StaticReadout"), Close);
        Formula signature = Seq(Open,
            realization, Dot, F.Id("readout"), Open, firstIndex, Comma, Sp, model, Close,
            Comma, Sp,
            realization, Dot, F.Id("readout"), Open, secondIndex, Comma, Sp, model, Close,
            Close);
        Formula imageCard = Seq(Open, F.Id("Finset"), Dot, F.Id("univ"), Dot,
            F.Id("image"), Open, Lambda(Seq(model, Colon, Sp, carrier), signature), Close,
            Close, Dot, F.Id("card"));
        return Seq(imageCard, Sp, Eq, Sp, D(3));
    }

    private static Formula AgreesFormula()
    {
        Formula first = Seq(Open, D(0), Colon, Sp, Call("Fin", D(3)), Close);
        return Seq(Neg, Sp, F.Id("staticExactExperimentRealization"), Dot,
            F.Id("toPrimitiveBundle"), Dot, F.Id("agrees"), Open,
            first, Comma, Sp, D(1), Close);
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);
}
