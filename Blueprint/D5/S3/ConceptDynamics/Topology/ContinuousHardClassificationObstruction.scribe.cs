using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class ContinuousHardClassificationObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/ContinuousHardClassificationObstruction."
            + "continuous_hard_classification_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonconstant discrete classifier continuously factored through a representation "
            + "forces a topological or continuity obstruction.",
        H("Continuous Hard Classification Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("continuous-hard-classification-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("Nonconstant hard classification requires a structural obstruction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The classifier is publicly required to factor as a decoder after a "
                        + "continuous representation. If the realized representation image is "
                        + "connected, the decoder is continuous, and the output topology is "
                        + "discrete, the decoder restricted to that image is constant by the "
                        + "imported connected-to-discrete rigidity theorem.")),
                Paragraph(Text(
                    "Composing that constant restriction with the representation makes the "
                        + "classifier constant on the entire object domain. This proves the "
                        + "first clause directly on the factorized classifier rather than on an "
                        + "unrelated special case.")),
                Paragraph(Text(
                    "For the contrapositive clause, a connected object domain has connected "
                        + "image under the continuous representation. Therefore a witnessed "
                        + "nonconstant classifier forces at least one listed obstruction: the "
                        + "realized representation is disconnected, the decoder is discontinuous, "
                        + "the output is nondiscrete, or the object domain is disconnected."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula objectType = F.Id("X");
        Formula representationType = F.Id("B");
        Formula outputType = F.Id("Y");
        Formula representation = F.Id("C");
        Formula decoder = F.Id("f");
        Formula classifier = F.Id("T");
        Formula first = F.Id("x");
        Formula second = F.Id("xPrime");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula factorization = Seq(
            classifier, Sp, Eq, Sp, decoder, Sp, Circ, Sp, representation);
        Formula representationContinuous = Call("Continuous", representation);
        Formula decoderContinuous = Call("Continuous", decoder);
        Formula connectedRepresentation =
            Call("IsConnected", Call("range", representation));
        Formula discreteOutput = Call("DiscreteTopology", outputType);
        Formula connectedObjects = Call("IsConnected", objectType);
        Formula classifierConstant = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, objectType, Comma, Sp,
            Apply(classifier, first), Sp, Eq, Sp, Apply(classifier, second));
        Formula nonconstant = Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, objectType, Comma, Sp,
            Apply(classifier, first), Sp, Neq, Sp, Apply(classifier, second));
        Formula constantClause = Seq(
            Open, decoderContinuous, Sp, Land, Sp, connectedRepresentation, Sp, Land, Sp,
            discreteOutput, Close, Sp, Rightarrow, Sp, Open, classifierConstant, Close);
        Formula obstructionClause = Seq(
            Open, nonconstant, Close, Sp, Rightarrow, Sp,
            Open, Neg, Sp, connectedRepresentation, Sp, Lor, Sp,
            Neg, Sp, decoderContinuous, Sp, Lor, Sp,
            Neg, Sp, discreteOutput, Sp, Lor, Sp,
            Neg, Sp, connectedObjects, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, objectType, Comma, Sp, representationType, Comma, Sp,
            outputType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            representation, Colon, Sp, objectType, Sp, To, Sp, representationType,
            Comma, Sp, decoder, Colon, Sp, representationType, Sp, To, Sp, outputType,
            Comma, Sp, classifier, Colon, Sp, objectType, Sp, To, Sp, outputType, Comma,
            RowBreak, Grp(),
            Open, factorization, Sp, Land, Sp, representationContinuous, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            Open, constantClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, obstructionClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
