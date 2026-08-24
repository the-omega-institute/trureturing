using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ConullImageProbabilityIsomorphismDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula source = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula outputLaw = Nu;
        Formula sourceLaw = Mu;
        Formula embedding = F.Id("e");
        Formula rangeLaw = F.Id("rho");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula range = Call("range", readout);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, output, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Call("StandardBorel", source), Comma, Sp,
            Call("StandardBorel", output), Comma, RowBreak, Grp(),
            readout, Colon, Sp, source, Sp, To, Sp, output, Comma, Sp,
            Call("Measurable", readout), Comma, Sp,
            Call("Injective", readout), Comma, RowBreak, Grp(),
            outputLaw, Colon, Sp, Call("ProbabilityMeasure", output), Comma, Sp,
            Apply(outputLaw, range), Sp, Eq, Sp, D(1), Sp, Rightarrow,
            RowBreak, Grp(),
            embedding, Sp, Eq, Sp, Call("equivRange", readout), Comma, Sp,
            rangeLaw, Sp, Eq, Sp, Call("comap", F.Id("coe"), outputLaw),
            Comma, RowBreak, Grp(),
            Exists, Sp, sourceLaw, Colon, Sp, Call("ProbabilityMeasure", source),
            Comma, Sp,
            Call("map", readout, sourceLaw), Sp, Eq, Sp, outputLaw,
            Sp, Land, RowBreak, Grp(),
            Call("MeasurePreserving", embedding, sourceLaw, rangeLaw), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A conull measurable injection pulls a probability law back to its domain.",
            H("Conull Image Probability Isomorphism"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("conull-measurable-injection-probability-isomorphism"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/"
                            + "ConullImageProbabilityIsomorphism."
                            + "conull_measurable_injection_probability_isomorphism"),
                    H("A conull measurable injection is a probability isomorphism"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The standard Borel hypotheses turn the measurable injection q into "
                                + "a measurable embedding. Its canonical equivalence e identifies "
                                + "X directly with the measurable subtype range(q).")),
                        Paragraph(Text(
                            "The measure rho is constructed by pulling nu back along subtype "
                                + "inclusion. Full mass of range(q) makes its pushforward exactly "
                                + "nu, and therefore makes rho a probability measure.")),
                        Paragraph(Text(
                            "Mapping rho back through the measurable inverse of e constructs mu. "
                                + "The public conclusions state both map(q, mu) = nu and that e is "
                                + "measure-preserving from mu to rho, exposing the conull-space "
                                + "isomorphism rather than wrapping it in mere inhabitation."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
