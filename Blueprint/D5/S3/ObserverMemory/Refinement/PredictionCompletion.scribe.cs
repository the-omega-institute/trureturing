using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class PredictionCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observation refinement induces a unique surjective map of predictive completions.",
        H("Predictive Completion under Observation Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-refinement-predictive-completion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/PredictionCompletion."
                    + "observation_refinement_completion"),
                H("Refinement induces the canonical predictive quotient map"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the coarse readout is obtained by applying forget to the fine "
                        + "readout. Applying forget at every time sends equality of complete fine "
                        + "itineraries to equality of complete coarse itineraries.")),
                    Paragraph(Text(
                        "The repository theorem relative_identity_refinement then gives the "
                        + "unique surjection between the two kernel quotients and its projection "
                        + "factorization. Quotient induction verifies that the same map "
                        + "intertwines the induced update and current readout.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Setoid.map_of_le, Setoid.lift_unique, "
                        + "Quotient.map, and Quotient.lift through the imported repository "
                        + "modules. Loogle and third-party searches found no declaration "
                        + "combining the relation, uniqueness, surjectivity, and both "
                        + "intertwining equations."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula BarredSubscript(Formula value, Formula index) =>
        Seq(Overline, Grp(value), Underscore, Grp(index));

    private static Formula Barred(Formula value) => Seq(Overline, Grp(value));

    private static Formula RefinementFormula()
    {
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula h = F.Id("h");
        Formula kappa = F.Id("kappa");
        Formula relationQ = Subscript(F.Id("R"), q);
        Formula relationR = Subscript(F.Id("R"), r);
        Formula stateQ = Subscript(F.Id("Z"), q);
        Formula stateR = Subscript(F.Id("Z"), r);
        Formula projectionQ = Subscript(Pi, q);
        Formula projectionR = Subscript(Pi, r);
        Formula updateQ = BarredSubscript(Tau, q);
        Formula updateR = BarredSubscript(Tau, r);
        Formula readoutQ = Barred(q);
        Formula readoutR = Barred(r);

        return Disp(Seq(
            r, Sp, Eq, Sp, h, Sp, Circ, Sp, q, Sp, Rightarrow, Esc,
            relationQ, Sp, Subseteq, Sp, relationR, Sp, Land, Esc,
            Exists, Bang, Sp, kappa, Colon, Sp, stateQ, Sp, To, Sp, stateR,
            Comma, Esc,
            Call("Surjective", kappa), Sp, Land, Esc,
            projectionR, Sp, Eq, Sp, kappa, Sp, Circ, Sp, projectionQ,
            Sp, Land, Esc,
            kappa, Sp, Circ, Sp, updateQ, Sp, Eq, Sp,
            updateR, Sp, Circ, Sp, kappa, Sp, Land, Esc,
            readoutR, Sp, Circ, Sp, kappa, Sp, Eq, Sp,
            h, Sp, Circ, Sp, readoutQ, Dot));
    }
}
