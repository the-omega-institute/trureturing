using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class MarginalActionEntropyCausalContrastDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Information/MarginalActionEntropyCausalContrast."
            + "marginal_action_entropy_causal_contrast";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marginal action entropy does not determine causal control.",
        H("Equal Action Entropy, Different Causal Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("marginal-action-entropy-causal-contrast"),
            DeclarationHandle.Create(Declaration),
            H("Equal marginal action entropy does not identify internal control"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state consists of a uniform hidden bit and independent uniform noise. "
                        + "One model copies the noise while the other copies the hidden bit.")),
                Paragraph(Text(
                    "Their marginal action entropies agree, but intervention on the hidden bit "
                        + "leaves the first action law fixed and changes the second."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula one = D(1);
        Formula two = D(2);
        Formula four = D(4);
        Formula state = F.Id("x");
        Formula bit = F.Id("m");
        Formula noise = F.Id("u");
        Formula output = F.Id("a");
        Formula model = F.Id("f");
        Formula stateLaw = F.Id("mu");
        Formula noiseLaw = F.Id("nu");
        Formula externalModel = new Formula.Subscript(F.Id("f"), F.Id("ext"));
        Formula internalModel = new Formula.Subscript(F.Id("f"), F.Id("int"));
        Formula external = externalModel;
        Formula intervention = F.Id("J");
        Formula boolType = F.Id("Bool");
        Formula boolPair = Seq(boolType, Sp, Times, Sp, boolType);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula stateFunction = new Formula.TypeArrow(boolPair, real);
        Formula modelFunction = new Formula.TypeArrow(boolPair, boolType);
        Formula noiseFunction = new Formula.TypeArrow(boolType, real);

        Formula definitions = Seq(
            state, Sp, Colon, Sp, boolPair, Comma, Sp,
            stateLaw, Sp, Colon, Sp, stateFunction, Comma, Sp,
            Apply(stateLaw, state), Sp, Eq, Sp, new Formula.Fraction(one, four),
            Comma, RowBreak, Grp(),
            externalModel, Sp, Colon, Sp, modelFunction, Comma, Sp,
            internalModel, Sp, Colon, Sp, modelFunction, Comma, RowBreak, Grp(),
            Apply(external, state), Sp, Eq, Sp, Call("snd", state), Comma, Sp,
            Apply(internalModel, state), Sp, Eq, Sp, Call("fst", state),
            Comma, RowBreak, Grp(),
            noiseLaw, Sp, Colon, Sp, noiseFunction, Comma, Sp,
            Apply(noiseLaw, noise), Sp, Eq, Sp, new Formula.Fraction(one, two),
            Comma, RowBreak, Grp(),
            intervention, Sp, Colon, Sp,
            new Formula.TypeArrow(modelFunction,
                new Formula.TypeArrow(boolType, noiseFunction)), Comma, Sp,
            Apply(intervention, model, bit, output), Sp, Eq, Sp,
            Call("pushforward", Seq(
                noise, Sp, Mapsto, Sp, Apply(model, Seq(bit, Comma, Sp, noise))),
                noiseLaw),
            Colon, RowBreak, Grp());

        Formula conclusion = Seq(
            Call("shannonEntropy", Call("conceptLaw", stateLaw, external)),
            Sp, Eq, Sp,
            Call("shannonEntropy", Call("conceptLaw", stateLaw, internalModel)),
            Sp, Land, RowBreak, Grp(),
            Apply(intervention, external, F.Id("false")), Sp, Eq, Sp,
            Apply(intervention, external, F.Id("true")),
            Sp, Land, RowBreak, Grp(),
            Apply(intervention, internalModel, F.Id("false")), Sp, Neq, Sp,
            Apply(intervention, internalModel, F.Id("true")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            definitions, conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
